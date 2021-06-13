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

use std::borrow::Cow;
use std::convert::TryFrom;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Display};
use std::str::FromStr;

#[derive(PartialEq, Copy, Clone, Debug)]
enum Prefix {
    SingleDash,
    DoubleDash,
}

#[derive(Clone, Debug)]
struct Arg<'a> {
    prefix: Prefix,
    name: &'a str,
    eq: Option<bool>,
    quotes: Option<char>,
    value: Option<&'a str>,
    #[cfg(feature = "combined-flags")]
    combined: bool,
}

#[derive(Clone, Debug)]
struct KeyQuery<'a> {
    prefix: Prefix,
    query: &'a str,
}

impl<'a> KeyQuery<'a> {
    fn new_short(query: &'a str) -> Self {
        Self {
            prefix: Prefix::SingleDash,
            query,
        }
    }
}

impl<'a> TryFrom<&'a str> for KeyQuery<'a> {
    type Error = Error;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        if s.starts_with("--") && s.len() > 2 {
            Ok(KeyQuery {
                prefix: Prefix::DoubleDash,
                query: &s[2..],
            })
        } else if s.starts_with('-') && s.len() == 2 {
            Ok(KeyQuery {
                prefix: Prefix::SingleDash,
                query: &s[1..],
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

impl<'a> Arg<'a> {
    fn new(s: &'a str) -> Result<Option<Self>, Error> {
        // TODO should be implement as From str

        if !s.starts_with('-') {
            return Ok(None);
        }
        // Starts by parsing it as flag, overwrite later if necessary
        let mut prefix = Prefix::SingleDash;
        let mut start_name_idx = 1;

        if s.starts_with("--") {
            prefix = Prefix::DoubleDash;
            start_name_idx = 2;
        }

        let mut eq = None;
        let quotes = None;
        let mut value = None;
        let mut name = &s[start_name_idx..];

        #[cfg(feature = "eq-separator")]
        {
            if let Some(eq_idx) = s.find('=') {
                name = &s[start_name_idx..eq_idx];
                eq = Some(true);
                // worst case, it's the end of the string, it won't panic
                let value_as_str = &s[eq_idx + 1..];
                value = Some(value_as_str);

                // Check for quoted value.
                if let Some(c) = value_as_str.get(..1) {
                    if c == "\"" || c == "'" {
                        // A closing quote must be the same as an opening one.
                        if value_as_str.len() > 1 && value_as_str.ends_with(c) {
                            value = Some(&value_as_str[1..value_as_str.len() - 1]);
                        } else {
                            value = Some("");
                        }
                    }
                }

                if value == Some("") {
                    value = None;
                }
            }
        }

        #[cfg(feature = "combined-flags")]
        let combined = prefix == Prefix::SingleDash && name.len() > 1;

        Ok(Some(Arg {
            prefix,
            name,
            eq,
            quotes,
            value,
            #[cfg(feature = "combined-flags")]
            combined,
        }))
    }

    fn contains(&self, k: &KeyQuery) -> bool {
        // KeyQuery is guaranteed to be either --long-query or -s (short)
        // It's up to the caller to split a combined-flags query into
        // multiple calls to this method (e.g. -vvv as query is not allowed)

        match (self.prefix, k.prefix) {
            (Prefix::DoubleDash, Prefix::DoubleDash) => self.name == k.query,
            #[cfg(not(feature = "combined-flags"))]
            (Prefix::SingleDash, Prefix::SingleDash) => self.name == k.query,
            #[cfg(feature = "combined-flags")]
            (Prefix::SingleDash, Prefix::SingleDash) => {
                if self.combined {
                    self.name.contains(k.query)
                } else {
                    self.name == k.query
                }
            }
            _ => false,
        }
    }
}

impl<'a> Display for Arg<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut quote = "";
        let quote_as_char: [u8; 1];
        if let Some(q) = self.quotes {
            // we decoded it from utf8 and it represents a single char, ascii
            quote_as_char = [q as u8];
            quote = std::str::from_utf8(&quote_as_char).unwrap();
        }

        write!(
            f,
            "{}{}{}{}{}{}",
            match self.prefix {
                Prefix::SingleDash => "-",
                Prefix::DoubleDash => "--",
            },
            self.name,
            if self.eq.is_none() { "" } else { "=" },
            quote,
            if let Some(v) = self.value { v } else { "" },
            quote,
        )
    }
}

#[cfg(feature = "combined-flags")]
fn consume<'a, 'b>(
    arg: &'a Arg<'a>,
    k: &'b KeyQuery<'b>,
) -> (Option<Cow<'a, str>>, Option<Cow<'b, KeyQuery<'b>>>) {
    if arg.prefix == Prefix::SingleDash && k.prefix == Prefix::SingleDash {
        // Combined flags. `k` could be "-vvv" and we have to create
        // a new Arg without the removed occurrences.

        let k_char = k.query.chars().next().unwrap();
        let k_len = k.query.len();
        let n = arg.name.matches(k_char).count();
        let arg_fully_consumed = n == arg.name.len() && n <= k_len;
        let query_fully_consumed = k_len <= n;

        return match (arg_fully_consumed, query_fully_consumed) {
            (true, true) => (None, None),
            (false, false) => (
                Some(Cow::Owned(arg.name.replacen(k_char, "", k_len))),
                Some(Cow::Owned(KeyQuery::new_short(&k.query[..k_len - n]))),
            ),
            (true, false) => (
                None,
                Some(Cow::Owned(KeyQuery::new_short(&k.query[..k_len - n]))),
            ),
            (false, true) => (Some(Cow::Owned(arg.name.replacen(k_char, "", k_len))), None),
        };
    }

    if arg.contains(k) {
        (None, None)
    } else {
        (Some(Cow::Borrowed(arg.name)), Some(Cow::Borrowed(k)))
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
            Error::MissingOption(key) => {
                if key.second() == &Query::Empty {
                    write!(f, "the '{}' option must be set", key.first())
                } else {
                    write!(
                        f,
                        "the '{}/{}' option must be set",
                        key.first(),
                        key.second()
                    )
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
        for k in keys.0.iter() {
            // XXX TODO pre-provide KeyQuery items
            if *k == Query::Empty {
                continue;
            }
            let k = KeyQuery::try_from(k.to_str()).unwrap();

            #[cfg(feature = "combined-flags")]
            let mut to_swap = Vec::new();

            // for each parameter provided (e.g. [--width=10, -v, --quiet])
            for (idx, param_ostr) in self.0.iter().enumerate() {
                // if we can decode it as a proper string
                if let Some(param) = param_ostr.to_str() {
                    // if it looks like an argument (some variation of "starts with -")
                    if let Ok(Some(arg)) = Arg::new(param) {
                        #[cfg(not(feature = "combined-flags"))]
                        if arg.contains(&k) {
                            self.0.remove(idx);
                            return true;
                        }

                        #[cfg(feature = "combined-flags")]
                        if arg.contains(&k) {
                            // consume as much `k` as possible from `arg`
                            let (maybe_new_name, maybe_new_k) = consume(&arg, &k);

                            if let Some(new_name) = maybe_new_name {
                                to_swap.push((idx, Some(new_name.into_owned())));
                            } else {
                                to_swap.push((idx, None));
                            }

                            if maybe_new_k.is_none() {
                                // We fully consumed the query (e.g. -k or -vvv)
                                // and we can apply the consumption

                                for (swap_idx, maybe_new_name) in to_swap.into_iter().rev() {
                                    if let Some(new_name) = maybe_new_name {
                                        let mut new_arg =
                                            Arg::new(self.0[swap_idx].to_str().unwrap())
                                                .unwrap()
                                                .unwrap();
                                        new_arg.name = &new_name;
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
        if let Some((idx, key)) = self.index_of(keys) {
            // Parse a `--key value` pair.

            let value = match self.0.get(idx + 1) {
                Some(v) => v,
                None => return Err(Error::OptionWithoutAValue(key)),
            };

            let value = os_to_str(value)?;
            Ok(Some((value, PairKind::TwoArguments, idx)))
        } else if let Some((idx, key)) = self.index_of2(keys) {
            // Parse a `--key=value` or `-Kvalue` pair.

            let value = &self.0[idx];

            // Only UTF-8 strings are supported in this method.
            let value = value.to_str().ok_or_else(|| Error::NonUtf8Argument)?;

            let mut value_range = key.len()..value.len();

            if value.as_bytes().get(value_range.start) == Some(&b'=') {
                #[cfg(feature = "eq-separator")]
                {
                    value_range.start += 1;
                }
                #[cfg(not(feature = "eq-separator"))]
                return Err(Error::OptionWithoutAValue(key));
            } else {
                // Key must be followed by `=` if not `short-space-opt`
                #[cfg(not(feature = "short-space-opt"))]
                return Err(Error::OptionWithoutAValue(key));
            }

            // Check for quoted value.
            if let Some(c) = value.as_bytes().get(value_range.start).cloned() {
                if c == b'"' || c == b'\'' {
                    value_range.start += 1;

                    // A closing quote must be the same as an opening one.
                    if ends_with(&value[value_range.start..], c) {
                        value_range.end -= 1;
                    } else {
                        return Err(Error::OptionWithoutAValue(key));
                    }
                }
            }

            // Check length, otherwise String::drain will panic.
            if value_range.end - value_range.start == 0 {
                return Err(Error::OptionWithoutAValue(key));
            }

            // Extract `value` from `--key="value"`.
            let value = &value[value_range];

            if value.is_empty() {
                return Err(Error::OptionWithoutAValue(key));
            }

            Ok(Some((value, PairKind::SingleArgument, idx)))
        } else {
            Ok(None)
        }
    }

    // The whole logic must be type-independent to prevent monomorphization.
    #[cfg(not(any(feature = "eq-separator", feature = "short-space-opt")))]
    #[inline(never)]
    fn find_value(&mut self, keys: &Keys) -> Result<Option<(&str, PairKind, usize)>, Error> {
        if let Some((idx, key)) = self.index_of(keys) {
            // Parse a `--key value` pair.

            let value = match self.0.get(idx + 1) {
                Some(v) => v,
                None => return Err(Error::OptionWithoutAValue(key)),
            };

            let value = os_to_str(value)?;
            Ok(Some((value, PairKind::TwoArguments, idx)))
        } else {
            Ok(None)
        }
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

        for key in &keys.0 {
            if key != "" {
                if let Some(i) = self.0.iter().position(|v| v == key.to_str()) {
                    return Some((i, key.to_str()));
                }
            }
        }

        None
    }

    #[cfg(any(feature = "eq-separator", feature = "short-space-opt"))]
    #[inline(never)]
    fn index_of2(&self, keys: &Keys) -> Option<(usize, &'static str)> {
        // Loop unroll to save space.

        if keys.first() != "" {
            if let Some(i) = self.0.iter().position(|v| index_predicate(v, keys.first())) {
                return Some((i, keys.first().to_str()));
            }
        }

        if keys.second() != "" {
            if let Some(i) = self
                .0
                .iter()
                .position(|v| index_predicate(v, keys.second()))
            {
                return Some((i, keys.second().to_str()));
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

#[cfg(feature = "eq-separator")]
#[inline(never)]
fn starts_with_plus_eq(text: &OsStr, q: &Query) -> bool {
    if let Some(s) = text.to_str() {
        let prefix = q.to_str();
        if s.get(0..prefix.len()) == Some(prefix) {
            if s.as_bytes().get(prefix.len()) == Some(&b'=') {
                return true;
            }
        }
    }

    false
}

#[cfg(feature = "short-space-opt")]
#[inline(never)]
fn starts_with_short_prefix(text: &OsStr, prefix: &Query) -> bool {
    match prefix {
        Query::Long(_) => false,
        _ => {
            if let Some(s) = text.to_str() {
                return s.starts_with(prefix.to_str());
            }
            false
        }
    }
}

#[cfg(all(feature = "eq-separator", feature = "short-space-opt"))]
#[inline]
fn index_predicate(text: &OsStr, prefix: &Query) -> bool {
    starts_with_plus_eq(text, prefix) || starts_with_short_prefix(text, prefix)
}
#[cfg(all(feature = "eq-separator", not(feature = "short-space-opt")))]
#[inline]
fn index_predicate(text: &OsStr, prefix: &Query) -> bool {
    starts_with_plus_eq(text, prefix)
}
#[cfg(all(feature = "short-space-opt", not(feature = "eq-separator")))]
#[inline]
fn index_predicate(text: &OsStr, prefix: &Query) -> bool {
    starts_with_short_prefix(text, prefix)
}

#[cfg(any(feature = "eq-separator", feature = "short-space-opt"))]
#[inline]
fn ends_with(text: &str, c: u8) -> bool {
    if text.is_empty() {
        false
    } else {
        text.as_bytes()[text.len() - 1] == c
    }
}

#[inline]
fn os_to_str(text: &OsStr) -> Result<&str, Error> {
    text.to_str().ok_or_else(|| Error::NonUtf8Argument)
}

#[derive(PartialEq, Clone, Debug)]
enum Query {
    Short(&'static str, char),
    Long(&'static str),
    Empty,
    #[cfg(feature = "combined-flags")]
    CombinedFlags(&'static str, Vec<char>),
}

impl Query {
    fn to_str(&self) -> &'static str {
        match *self {
            Query::Empty => "",
            Query::Short(x, _) => x,
            Query::Long(x) => x,
            #[cfg(feature = "combined-flags")]
            Query::CombinedFlags(x, _) => x,
        }
    }
}

impl PartialEq<str> for Query {
    fn eq(&self, other: &str) -> bool {
        other == self.to_str()
    }
}

impl Display for Query {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Query::Short(x, _) => x,
            Query::Long(x) => x,
            Query::Empty => "",
            #[cfg(feature = "combined-flags")]
            Query::CombinedFlags(x, _) => x,
        })
    }
}

/// A keys container.
///
/// Should not be used directly.
#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct Keys([Query; 2]);

impl Keys {
    #[inline]
    fn first(&self) -> &Query {
        &self.0[0]
    }

    #[inline]
    fn second(&self) -> &Query {
        &self.0[1]
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

        #[cfg(feature = "combined-flags")]
        let first = Query::CombinedFlags(v[0], v[0].chars().collect());

        #[cfg(not(feature = "combined-flags"))]
        let first = Query::Short(v[0], v[0].chars().nth(1).unwrap());

        Keys([first, Query::Long(&v[1])])
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

        let k = if v.starts_with("--") {
            Query::Long(&v)
        } else {
            Query::Short(&v, v.chars().next().unwrap())
        };
        Keys([k, Query::Empty])
    }
}
