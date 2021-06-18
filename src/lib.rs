/*!
An ultra simple CLI arguments parser.

If you think that this library doesn't support some feature, it's probably intentional.

- No help generation.
- Only flags, options, free arguments and subcommands are supported.
- No combined flags (like `-vvv` or `-abc`).
- Options can be separated by a space, `=` or nothing. See build features.
- Arguments can be in any order.
- Non UTF-8 arguments are supported.

## Build features

- `eq-separator`

  Allows parsing arguments separated by `=`. Enabled by default.<br/>
  This feature adds about 1KiB to the resulting binary.

- `short-space-opt`

  Makes the space between short keys and their values optional (e.g. `-w10`).<br/>
  If `eq-separator` is enabled, then it takes precedence and the '=' is not included.<br/>
  If `eq-separator` is disabled, then `-K=value` gives an error instead of returning `"=value"`.<br/>
  The optional space is only applicable for short keys because `--keyvalue` would be ambiguous.

- `combined-flags`
  Allows combination of flags, e.g. `-abc` instead of `-a -b -c`. If `short-space-opt` or `eq-separator` are enabled, you must parse flags after values, to prevent ambiguities.
*/

#![doc(html_root_url = "https://docs.rs/pico-args/0.4.2")]
#![forbid(unsafe_code)]
#![warn(missing_docs)]

use std::convert::TryFrom;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Display};
use std::str::FromStr;

#[cfg(feature = "combined-flags")]
use std::borrow::Cow;

#[derive(PartialEq, Copy, Clone, Debug)]
enum Prefix {
    SingleDash,
    DoubleDash,
}

#[derive(Clone, Debug)]
struct Arg<'a> {
    // represent `-` or `--`
    prefix: Prefix,
    // the part right of the prefix
    rest: &'a str,
    // the full string
    repr: &'a str,
    // the index of the first non-ascii/alphabetic character
    idx_non_alpha: Option<usize>,
}

#[derive(Clone, Debug)]
struct KeyQuery {
    // represent `-` or `--`
    prefix: Prefix,
    // the part right of the prefix
    query: &'static str,
    // the full string
    repr: &'static str,
}

impl TryFrom<&'static str> for KeyQuery {
    type Error = Error;

    fn try_from(s: &'static str) -> Result<Self, Self::Error> {
        if s.starts_with("--") && s.len() > 2 {
            Ok(KeyQuery {
                prefix: Prefix::DoubleDash,
                query: &s[2..],
                repr: &s,
            })
        } else if s.starts_with('-') && s.len() == 2 {
            Ok(KeyQuery {
                prefix: Prefix::SingleDash,
                query: &s[1..],
                repr: &s,
            })
        } else {
            #[cfg(feature = "combined-flags")]
            {
                // XXX Check must be the same character repeated
                // or `consume` will fail in weird ways
                if s.starts_with('-') && s.len() > 2 {
                    return Ok(KeyQuery {
                        prefix: Prefix::SingleDash,
                        query: &s[1..],
                        repr: &s,
                    });
                }
            }

            Err(Error::Utf8ArgumentParsingFailed {
                value: s.to_owned(),
                cause: "wrong format".to_owned(),
            })
        }
    }
}

impl<'a> TryFrom<&'a OsString> for Arg<'a> {
    type Error = Error;

    fn try_from(s: &'a OsString) -> Result<Self, Self::Error> {
        let s = os_to_str(s)?;
        Arg::try_from(s)
    }
}

impl<'a> TryFrom<&'a str> for Arg<'a> {
    type Error = Error;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        if !s.starts_with('-') {
            return Err(Error::NotAnOption);
        }

        let (prefix, rest) = if s.starts_with("--") {
            (Prefix::DoubleDash, &s[2..])
        } else {
            (Prefix::SingleDash, &s[1..])
        };

        let idx_non_alpha = if prefix == Prefix::SingleDash {
            rest.find(|c: char| !c.is_ascii_alphabetic())
        } else {
            rest.find(|c: char| !c.is_ascii_alphanumeric())
        };

        Ok(Arg {
            prefix,
            rest,
            repr: s,
            idx_non_alpha,
        })
    }
}

impl<'a> Arg<'a> {
    // Search for boolean flags
    //
    // KeyQuery `-v` will match Arg `-v` (and also `-vvv` or `-iv` if feature
    // combined-flags is on).
    // It will wrongly match a short-opt parameter, like -iverymuch, so it's up
    // to the caller to first consume options with parameters before calling
    // this function.
    fn contains(&self, k: &KeyQuery) -> bool {
        self.index_of(k).is_some()
    }

    fn index_of(&self, k: &KeyQuery) -> Option<(usize, usize)> {
        #[cfg(not(feature = "combined-flags"))]
        let query = k.query;

        #[cfg(feature = "combined-flags")]
        let query = if k.prefix == Prefix::SingleDash {
            &k.query[0..1]
        } else {
            k.query
        };

        let start_idx = match (self.prefix, k.prefix) {
            (Prefix::DoubleDash, Prefix::DoubleDash) => {
                if &self.rest[0..self.idx_non_alpha.unwrap_or(self.rest.len())] == query {
                    Some(0)
                } else {
                    None
                }
            }
            #[cfg(not(feature = "combined-flags"))]
            (Prefix::SingleDash, Prefix::SingleDash) => {
                if self.rest.starts_with(query) {
                    Some(0)
                } else {
                    None
                }
            }
            #[cfg(feature = "combined-flags")]
            (Prefix::SingleDash, Prefix::SingleDash) => {
                // stop at idx_non_alpha to avoid matching stuff like `-v` in `-abc=v`
                self.rest[0..self.idx_non_alpha.unwrap_or(self.rest.len())].find(query)
            }
            _ => None,
        };

        start_idx.map(|s_idx| (s_idx, s_idx + k.query.len()))
    }

    #[cfg(all(not(feature = "eq-separator"), not(feature = "short-space-opt")))]
    fn find_value_for(&self, k: &KeyQuery) -> Option<&str> {
        None
    }

    #[cfg(any(feature = "eq-separator", feature = "short-space-opt"))]
    fn find_value_for(&self, k: &KeyQuery) -> Option<&'a str> {
        // -w
        // -w=10    // eq-separator
        // -w='10'
        // -w="10"
        // -w10     // short-space-opt
        // -w'10'
        // -w"10"
        // -w"=10"
        // -iw      // combined-args
        // -iw=10   // combined-args eq-separator
        // -iw10    // combined-args short-space-opt
        // ...      // similar to the first ones, but for combined-args
        // --width  //follow same rules as not combined-args options
        //
        // -iw=foo  // should error out if eq-separator is off
        // -iw=foo  // should not match -f
        // -w'foo"  // non-matching quotes should error out

        // First get the option bounds (if it's even there)
        let (_, end_idx) = match self.index_of(k) {
            Some(x) => x,
            _ => return None,
        };

        if end_idx == self.rest.len() {
            // no more text to search into
            return None;
        }

        // Start by assigning everything (maybe is -w10, or --width=10, -w'10', ...)
        let mut value = &self.rest[end_idx..];

        // Do we accept the value? Anything to drop? Think `--width=10` or `-w10`
        #[cfg(feature = "eq-separator")]
        {
            value = match value.chars().next().unwrap() {
                '=' if value.len() == 1 => return None,
                '=' => &value[1..],
                #[cfg(feature = "short-space-opt")]
                _ => value,
                #[cfg(not(feature = "short-space-opt"))]
                _ => return None,
            };
        }
        // Check for quotes
        if let Some(c) = value.get(..1) {
            if c == "\"" || c == "'" {
                // A closing quote must be the same as an opening one
                if value.len() > 1 && value.ends_with(c) {
                    value = &value[1..value.len() - 1];
                } else {
                    value = "";
                }
            }
        }

        if value.is_empty() {
            None
        } else {
            Some(value)
        }
    }
}

impl<'a> Display for Arg<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.repr)
    }
}

#[cfg(feature = "combined-flags")]
fn consume<'a, 'b>(
    arg: &'a Arg<'a>,
    k: &'b KeyQuery,
) -> (Option<Cow<'a, str>>, Option<Cow<'b, KeyQuery>>) {
    if arg.prefix == Prefix::SingleDash && k.prefix == Prefix::SingleDash {
        // Combined flags. `k.repr` could be "-vvv" and we have to create
        // a new Arg without the removed occurrences.

        let k_char = k.query.chars().next().unwrap();
        let k_len = k.query.len();
        let n = arg.rest.matches(k_char).count();
        let arg_fully_consumed = n == arg.rest.len() && n <= k_len;
        let query_fully_consumed = k_len <= n;

        return match (arg_fully_consumed, query_fully_consumed) {
            (true, true) => (None, None),
            (false, false) => (
                Some(Cow::Owned(arg.repr.replacen(k_char, "", k_len))),
                Some(Cow::Owned(
                    KeyQuery::try_from(&k.repr[..k.repr.len() - n]).unwrap(),
                )),
            ),
            (true, false) => (
                None,
                Some(Cow::Owned(
                    KeyQuery::try_from(&k.repr[..k.repr.len() - n]).unwrap(),
                )),
            ),
            (false, true) => (Some(Cow::Owned(arg.repr.replacen(k_char, "", k_len))), None),
        };
    }

    if arg.contains(k) {
        (None, None)
    } else {
        (Some(Cow::Borrowed(arg.repr)), Some(Cow::Borrowed(k)))
    }
}

/// A list of possible errors.
#[derive(Clone, Debug)]
pub enum Error {
    /// Arguments must be a valid UTF-8 strings.
    NonUtf8Argument,

    /// A missing free-standing argument.
    MissingArgument,

    /// A missing option.
    MissingOption(Keys),

    /// An option without a value.
    OptionWithoutAValue(&'static str),

    /// Failed to parse a UTF-8 free-standing argument.
    #[allow(missing_docs)]
    Utf8ArgumentParsingFailed { value: String, cause: String },

    /// Failed to parse a raw free-standing argument.
    #[allow(missing_docs)]
    ArgumentParsingFailed { cause: String },

    /// Not an option.
    NotAnOption,
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::NonUtf8Argument => {
                write!(f, "argument is not a UTF-8 string")
            }
            Error::MissingArgument => {
                write!(f, "free-standing argument is missing")
            }
            Error::MissingOption(keys) => {
                if let (Some(first_key), Some(second_key)) = (keys.first(), keys.second()) {
                    write!(
                        f,
                        "the '{}/{}' option must be set",
                        first_key.repr, second_key.repr
                    )
                } else if let (Some(first_key), None) = (keys.first(), keys.second()) {
                    write!(f, "the '{}' option must be set", first_key.repr)
                } else {
                    // XXX this should have been catched on key creation
                    write!(f, "missing options to serch for")
                }
            }
            Error::OptionWithoutAValue(key) => {
                write!(f, "the '{}' option doesn't have an associated value", key)
            }
            Error::Utf8ArgumentParsingFailed { value, cause } => {
                write!(f, "failed to parse '{}' cause {}", value, cause)
            }
            Error::ArgumentParsingFailed { cause } => {
                write!(f, "failed to parse a binary argument cause {}", cause)
            }
            Error::NotAnOption => {
                write!(f, "attempted to parse an argument as if it was an option")
            }
        }
    }
}

impl std::error::Error for Error {}

#[derive(Clone, Copy, PartialEq)]
enum PairKind {
    #[cfg(any(feature = "eq-separator", feature = "short-space-opt"))]
    SingleArgument,
    TwoArguments,
}

/// An arguments parser.
#[derive(Clone, Debug)]
pub struct Arguments(Vec<OsString>);

impl Arguments {
    /// Creates a parser from a vector of arguments.
    ///
    /// The executable path **must** be removed.
    ///
    /// This can be used for supporting `--` arguments to forward to another program.
    /// See `examples/dash_dash.rs` for an example.
    pub fn from_vec(args: Vec<OsString>) -> Self {
        Arguments(args)
    }

    /// Creates a parser from [`env::args_os`].
    ///
    /// The executable path will be removed.
    ///
    /// [`env::args_os`]: https://doc.rust-lang.org/stable/std/env/fn.args_os.html
    pub fn from_env() -> Self {
        let mut args: Vec<_> = std::env::args_os().collect();
        args.remove(0);
        Arguments(args)
    }

    /// Parses the name of the subcommand, that is, the first positional argument.
    ///
    /// Returns `None` when subcommand starts with `-` or when there are no arguments left.
    ///
    /// # Errors
    ///
    /// - When arguments is not a UTF-8 string.
    pub fn subcommand(&mut self) -> Result<Option<String>, Error> {
        if self.0.is_empty() {
            return Ok(None);
        }

        if let Some(s) = self.0[0].to_str() {
            if s.starts_with('-') {
                return Ok(None);
            }
        }

        self.0
            .remove(0)
            .into_string()
            .map_err(|_| Error::NonUtf8Argument)
            .map(Some)
    }

    /// Checks that arguments contain a specified flag.
    ///
    /// Searches through all arguments, not only the first/next one.
    ///
    /// Calling this method "consumes" the flag: if a flag is present `n`
    /// times then the first `n` calls to `contains` for that flag will
    /// return `true`, and subsequent calls will return `false`.
    ///
    /// When the "combined-flags" feature is used, repeated letters count
    /// as repeated flags: `-vvv` is treated the same as `-v -v -v`, but
    /// it's consumed only if it matches as many times as the repetitions.
    ///
    /// This method should be called after having already consumed arguments
    /// with values (optional or not), otherwise you risk to count values
    /// as flags (e.g. --with-value=-x or --with-value -x would incorrectly
    /// match when using `contains("-x")`, and be consumed in the process).
    pub fn contains<A: Into<Keys>>(&mut self, keys: A) -> bool {
        self.contains_impl(&keys.into())
    }

    #[inline(never)]
    fn contains_impl(&mut self, keys: &Keys) -> bool {
        // for each user's provided key to match
        for k in keys.0.iter().filter_map(|k| k.as_ref()) {
            #[cfg(feature = "combined-flags")]
            let mut to_swap = Vec::new();

            // for each parameter provided (e.g. [--width=10, -v, --quiet])
            for (idx, param_ostr) in self.0.iter().enumerate() {
                // if we can parse it
                if let Ok(arg) = Arg::try_from(param_ostr) {
                    #[cfg(not(feature = "combined-flags"))]
                    if arg.contains(&k) {
                        self.0.remove(idx);
                        return true;
                    }

                    #[cfg(feature = "combined-flags")]
                    if arg.contains(&k) {
                        // consume as much `k` as possible from `arg`
                        let (maybe_new_arg_repr, maybe_new_k) = consume(&arg, &k);

                        if let Some(new_arg_repr) = maybe_new_arg_repr {
                            to_swap.push((idx, Some(new_arg_repr.into_owned())));
                        } else {
                            to_swap.push((idx, None));
                        }

                        if maybe_new_k.is_none() {
                            // We fully consumed the query (e.g. -k or -vvv)
                            // and we can apply the consumption

                            for (swap_idx, maybe_new_arg_repr) in to_swap.into_iter().rev() {
                                if let Some(new_arg_repr) = maybe_new_arg_repr {
                                    let s_ref: &str = new_arg_repr.as_ref();
                                    let new_arg = Arg::try_from(s_ref).unwrap();
                                    self.0[swap_idx] = OsString::from(new_arg.to_string());
                                } else {
                                    self.0.remove(swap_idx);
                                }
                            }

                            return true;
                        }
                    }
                }
            }
        }

        false
    }

    /// Parses a key-value pair using `FromStr` trait.
    ///
    /// This is a shorthand for `value_from_fn("--key", FromStr::from_str)`
    pub fn value_from_str<A, T>(&mut self, keys: A) -> Result<T, Error>
    where
        A: Into<Keys>,
        T: FromStr,
        <T as FromStr>::Err: Display,
    {
        self.value_from_fn(keys, FromStr::from_str)
    }

    /// Parses a key-value pair using a specified function.
    ///
    /// Searches through all argument, not only the first/next one.
    ///
    /// When a key-value pair is separated by a space, the algorithm
    /// will threat the next argument after the key as a value,
    /// even if it has a `-/--` prefix.
    /// So a key-value pair like `--key --value` is not an error.
    ///
    /// Must be used only once for each option.
    ///
    /// # Errors
    ///
    /// - When option is not present.
    /// - When key or value is not a UTF-8 string. Use [`value_from_os_str`] instead.
    /// - When value parsing failed.
    /// - When key-value pair is separated not by space or `=`.
    ///
    /// [`value_from_os_str`]: struct.Arguments.html#method.value_from_os_str
    pub fn value_from_fn<A: Into<Keys>, T, E: Display>(
        &mut self,
        keys: A,
        f: fn(&str) -> Result<T, E>,
    ) -> Result<T, Error> {
        let keys = keys.into();
        match self.opt_value_from_fn(keys.clone(), f) {
            Ok(Some(v)) => Ok(v),
            Ok(None) => Err(Error::MissingOption(keys.clone())),
            Err(e) => Err(e),
        }
    }

    /// Parses an optional key-value pair using `FromStr` trait.
    ///
    /// This is a shorthand for `opt_value_from_fn("--key", FromStr::from_str)`
    pub fn opt_value_from_str<A, T>(&mut self, keys: A) -> Result<Option<T>, Error>
    where
        A: Into<Keys>,
        T: FromStr,
        <T as FromStr>::Err: Display,
    {
        self.opt_value_from_fn(keys, FromStr::from_str)
    }

    /// Parses an optional key-value pair using a specified function.
    ///
    /// The same as [`value_from_fn`], but returns `Ok(None)` when option is not present.
    ///
    /// [`value_from_fn`]: struct.Arguments.html#method.value_from_fn
    pub fn opt_value_from_fn<A: Into<Keys>, T, E: Display>(
        &mut self,
        keys: A,
        f: fn(&str) -> Result<T, E>,
    ) -> Result<Option<T>, Error> {
        self.opt_value_from_fn_impl(&keys.into(), f)
    }

    #[inline(never)]
    fn opt_value_from_fn_impl<T, E: Display>(
        &mut self,
        keys: &Keys,
        f: fn(&str) -> Result<T, E>,
    ) -> Result<Option<T>, Error> {
        match self.find_value(keys)? {
            Some((value, kind, idx)) => {
                match f(value) {
                    Ok(value) => {
                        // Remove only when all checks are passed.
                        self.0.remove(idx);
                        if kind == PairKind::TwoArguments {
                            self.0.remove(idx);
                        }

                        Ok(Some(value))
                    }
                    Err(e) => Err(Error::Utf8ArgumentParsingFailed {
                        value: value.to_string(),
                        cause: error_to_string(e),
                    }),
                }
            }
            None => Ok(None),
        }
    }

    // The whole logic must be type-independent to prevent monomorphization.
    #[cfg(any(feature = "eq-separator", feature = "short-space-opt"))]
    #[inline(never)]
    fn find_value(&mut self, keys: &Keys) -> Result<Option<(&str, PairKind, usize)>, Error> {
        for key in keys.0.iter().filter_map(|k| k.as_ref()) {
            // for each parameter provided (e.g. [--width=10, -v, --quiet])
            for (idx, param_ostr) in self.0.iter().enumerate() {
                // if we can parse it
                if let Ok(arg) = Arg::try_from(param_ostr) {
                    if arg.repr == key.repr {
                        // expect a --key value pair

                        let value = match self.0.get(idx + 1) {
                            Some(v) => v,
                            None => return Err(Error::OptionWithoutAValue(key.repr)),
                        };

                        let value = os_to_str(value)?;
                        return Ok(Some((value, PairKind::TwoArguments, idx)));
                    } else if arg.contains(key) {
                        // expect a `--key=value` or `-Kvalue` pair

                        let value = arg.find_value_for(key);

                        return if let Some(value) = value {
                            Ok(Some((value, PairKind::SingleArgument, idx)))
                        } else {
                            Err(Error::OptionWithoutAValue(key.repr))
                        };
                    }
                }
            }
        }

        Ok(None)
    }

    /// Parses multiple key-value pairs into the `Vec` using `FromStr` trait.
    ///
    /// This is a shorthand for `values_from_fn("--key", FromStr::from_str)`
    pub fn values_from_str<A, T>(&mut self, keys: A) -> Result<Vec<T>, Error>
    where
        A: Into<Keys>,
        T: FromStr,
        <T as FromStr>::Err: Display,
    {
        self.values_from_fn(keys, FromStr::from_str)
    }

    /// Parses multiple key-value pairs into the `Vec` using a specified function.
    ///
    /// This functions can be used to parse arguments like:<br>
    /// `--file /path1 --file /path2 --file /path3`<br>
    /// But not `--file /path1 /path2 /path3`.
    ///
    /// Arguments can also be separated: `--file /path1 --some-flag --file /path2`
    ///
    /// This method simply executes [`opt_value_from_fn`] multiple times.
    ///
    /// An empty `Vec` is not an error.
    ///
    /// [`opt_value_from_fn`]: struct.Arguments.html#method.opt_value_from_fn
    pub fn values_from_fn<A: Into<Keys>, T, E: Display>(
        &mut self,
        keys: A,
        f: fn(&str) -> Result<T, E>,
    ) -> Result<Vec<T>, Error> {
        let keys = keys.into();

        let mut values = Vec::new();
        loop {
            match self.opt_value_from_fn(keys.clone(), f) {
                Ok(Some(v)) => values.push(v),
                Ok(None) => break,
                Err(e) => return Err(e),
            }
        }

        Ok(values)
    }

    /// Parses a key-value pair using a specified function.
    ///
    /// Unlike [`value_from_fn`], parses `&OsStr` and not `&str`.
    ///
    /// Must be used only once for each option.
    ///
    /// # Errors
    ///
    /// - When option is not present.
    /// - When value parsing failed.
    /// - When key-value pair is separated not by space.
    ///   Only [`value_from_fn`] supports `=` separator.
    ///
    /// [`value_from_fn`]: struct.Arguments.html#method.value_from_fn
    pub fn value_from_os_str<A: Into<Keys>, T, E: Display>(
        &mut self,
        keys: A,
        f: fn(&OsStr) -> Result<T, E>,
    ) -> Result<T, Error> {
        let keys = keys.into();
        match self.opt_value_from_os_str(keys.clone(), f) {
            Ok(Some(v)) => Ok(v),
            Ok(None) => Err(Error::MissingOption(keys.clone())),
            Err(e) => Err(e),
        }
    }

    /// Parses an optional key-value pair using a specified function.
    ///
    /// The same as [`value_from_os_str`], but returns `Ok(None)` when option is not present.
    ///
    /// [`value_from_os_str`]: struct.Arguments.html#method.value_from_os_str
    pub fn opt_value_from_os_str<A: Into<Keys>, T, E: Display>(
        &mut self,
        keys: A,
        f: fn(&OsStr) -> Result<T, E>,
    ) -> Result<Option<T>, Error> {
        self.opt_value_from_os_str_impl(&keys.into(), f)
    }

    #[inline(never)]
    fn opt_value_from_os_str_impl<T, E: Display>(
        &mut self,
        keys: &Keys,
        f: fn(&OsStr) -> Result<T, E>,
    ) -> Result<Option<T>, Error> {
        if let Some((idx, key)) = self.index_of(keys) {
            // Parse a `--key value` pair.

            let value = match self.0.get(idx + 1) {
                Some(v) => v,
                None => return Err(Error::OptionWithoutAValue(key)),
            };

            match f(value) {
                Ok(value) => {
                    // Remove only when all checks are passed.
                    self.0.remove(idx);
                    self.0.remove(idx);
                    Ok(Some(value))
                }
                Err(e) => Err(Error::ArgumentParsingFailed {
                    cause: error_to_string(e),
                }),
            }
        } else {
            Ok(None)
        }
    }

    /// Parses multiple key-value pairs into the `Vec` using a specified function.
    ///
    /// This method simply executes [`opt_value_from_os_str`] multiple times.
    ///
    /// Unlike [`values_from_fn`], parses `&OsStr` and not `&str`.
    ///
    /// An empty `Vec` is not an error.
    ///
    /// [`opt_value_from_os_str`]: struct.Arguments.html#method.opt_value_from_os_str
    /// [`values_from_fn`]: struct.Arguments.html#method.values_from_fn
    pub fn values_from_os_str<A: Into<Keys>, T, E: Display>(
        &mut self,
        keys: A,
        f: fn(&OsStr) -> Result<T, E>,
    ) -> Result<Vec<T>, Error> {
        let keys: Keys = keys.into();
        let mut values = Vec::new();
        loop {
            match self.opt_value_from_os_str(keys.clone(), f) {
                Ok(Some(v)) => values.push(v),
                Ok(None) => break,
                Err(e) => return Err(e),
            }
        }

        Ok(values)
    }

    #[inline(never)]
    fn index_of(&self, keys: &Keys) -> Option<(usize, &'static str)> {
        // Do not unroll loop to save space, because it creates a bigger file.
        // Which is strange, since `index_of2` actually benefits from it.

        for maybe_key in &keys.0 {
            if let Some(key) = maybe_key {
                if let Some(i) = self.0.iter().position(|v| v == key.repr) {
                    return Some((i, key.repr));
                }
            }
        }

        None
    }

    /// Parses a free-standing argument using `FromStr` trait.
    ///
    /// This is a shorthand for `free_from_fn(FromStr::from_str)`
    pub fn free_from_str<T>(&mut self) -> Result<T, Error>
    where
        T: FromStr,
        <T as FromStr>::Err: Display,
    {
        self.free_from_fn(FromStr::from_str)
    }

    /// Parses a free-standing argument using a specified function.
    ///
    /// Parses the first argument from the list of remaining arguments.
    /// Therefore, it's up to the caller to check if the argument is actually
    /// a free-standing one and not an unused flag/option.
    ///
    /// Sadly, there is no way to automatically check for flag/option.
    /// `-`, `--`, `-1`, `-0.5`, `--.txt` - all of this arguments can have different
    /// meaning depending on the caller requirements.
    ///
    /// Must be used only once for each argument.
    ///
    /// # Errors
    ///
    /// - When argument is not a UTF-8 string. Use [`free_from_os_str`] instead.
    /// - When argument parsing failed.
    /// - When argument is not present.
    ///
    /// [`free_from_os_str`]: struct.Arguments.html#method.free_from_os_str
    #[inline(never)]
    pub fn free_from_fn<T, E: Display>(&mut self, f: fn(&str) -> Result<T, E>) -> Result<T, Error> {
        self.opt_free_from_fn(f)?.ok_or(Error::MissingArgument)
    }

    /// Parses a free-standing argument using a specified function.
    ///
    /// The same as [`free_from_fn`], but parses `&OsStr` instead of `&str`.
    ///
    /// [`free_from_fn`]: struct.Arguments.html#method.free_from_fn
    #[inline(never)]
    pub fn free_from_os_str<T, E: Display>(
        &mut self,
        f: fn(&OsStr) -> Result<T, E>,
    ) -> Result<T, Error> {
        self.opt_free_from_os_str(f)?.ok_or(Error::MissingArgument)
    }

    /// Parses an optional free-standing argument using `FromStr` trait.
    ///
    /// The same as [`free_from_str`], but returns `Ok(None)` when argument is not present.
    ///
    /// [`free_from_str`]: struct.Arguments.html#method.free_from_str
    pub fn opt_free_from_str<T>(&mut self) -> Result<Option<T>, Error>
    where
        T: FromStr,
        <T as FromStr>::Err: Display,
    {
        self.opt_free_from_fn(FromStr::from_str)
    }

    /// Parses an optional free-standing argument using a specified function.
    ///
    /// The same as [`free_from_fn`], but returns `Ok(None)` when argument is not present.
    ///
    /// [`free_from_fn`]: struct.Arguments.html#method.free_from_fn
    #[inline(never)]
    pub fn opt_free_from_fn<T, E: Display>(
        &mut self,
        f: fn(&str) -> Result<T, E>,
    ) -> Result<Option<T>, Error> {
        if self.0.is_empty() {
            Ok(None)
        } else {
            let value = self.0.remove(0);
            let value = os_to_str(value.as_os_str())?;
            match f(&value) {
                Ok(value) => Ok(Some(value)),
                Err(e) => Err(Error::Utf8ArgumentParsingFailed {
                    value: value.to_string(),
                    cause: error_to_string(e),
                }),
            }
        }
    }

    /// Parses a free-standing argument using a specified function.
    ///
    /// The same as [`free_from_os_str`], but returns `Ok(None)` when argument is not present.
    ///
    /// [`free_from_os_str`]: struct.Arguments.html#method.free_from_os_str
    #[inline(never)]
    pub fn opt_free_from_os_str<T, E: Display>(
        &mut self,
        f: fn(&OsStr) -> Result<T, E>,
    ) -> Result<Option<T>, Error> {
        if self.0.is_empty() {
            Ok(None)
        } else {
            let value = self.0.remove(0);
            match f(value.as_os_str()) {
                Ok(value) => Ok(Some(value)),
                Err(e) => Err(Error::ArgumentParsingFailed {
                    cause: error_to_string(e),
                }),
            }
        }
    }

    /// Returns a list of remaining arguments.
    ///
    /// It's up to the caller what to do with them.
    /// One can report an error about unused arguments,
    /// other can use them for further processing.
    pub fn finish(self) -> Vec<OsString> {
        self.0
    }
}

// Display::to_string() is usually inlined, so by wrapping it in a non-inlined
// function we are reducing the size a bit.
#[inline(never)]
fn error_to_string<E: Display>(e: E) -> String {
    e.to_string()
}

#[inline]
fn os_to_str(text: &OsStr) -> Result<&str, Error> {
    text.to_str().ok_or_else(|| Error::NonUtf8Argument)
}

/// A keys container.
///
/// Should not be used directly.
#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct Keys([Option<KeyQuery>; 2]);

impl Keys {
    #[inline]
    fn first(&self) -> Option<&KeyQuery> {
        self.0[0].as_ref()
    }

    #[inline]
    fn second(&self) -> Option<&KeyQuery> {
        self.0[1].as_ref()
    }
}

impl From<[&'static str; 2]> for Keys {
    #[inline]
    fn from(v: [&'static str; 2]) -> Self {
        debug_assert!(v[0].starts_with("-"), "an argument should start with '-'");
        validate_shortflag(v[0]);
        debug_assert!(
            !v[0].starts_with("--"),
            "the first argument should be short"
        );
        debug_assert!(v[1].starts_with("--"), "the second argument should be long");

        // We're handling static strings, it's ok to panic if the format is wrong
        let first = KeyQuery::try_from(v[0]).unwrap();
        let second = KeyQuery::try_from(v[1]).unwrap();
        Keys([Some(first), Some(second)])
    }
}

fn validate_shortflag(short_key: &'static str) {
    let mut chars = short_key[1..].chars();
    if let Some(first) = chars.next() {
        debug_assert!(
            short_key.len() == 2 || chars.all(|c| c == first),
            "short keys should be a single character or a repeated character"
        );
    }
}

impl From<&'static str> for Keys {
    #[inline]
    fn from(v: &'static str) -> Self {
        debug_assert!(v.starts_with("-"), "an argument should start with '-'");
        if !v.starts_with("--") {
            validate_shortflag(v);
        }

        Keys([KeyQuery::try_from(v).ok(), None])
    }
}
