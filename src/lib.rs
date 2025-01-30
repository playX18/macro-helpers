
use lazy_regex::Captures;
use proc_macro2::{Group, Literal, Span, TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
    spanned::Spanned,
    Ident, Lit, LitInt,
};

/// MacroIf is a struct that represents the if statement in the macro.
///
///
/// ```rust
/// macro_if! {
///     if condition {
///         if_true
///     } else {
///         if_false
///     }
/// }
/// ```
struct MacroIf {
    pub condition: syn::Expr,
    pub if_true: proc_macro2::TokenStream,
    pub if_false: proc_macro2::TokenStream,
}

impl Parse for MacroIf {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _ = input.parse::<syn::Token![if]>()?;
        let condition = input.parse::<syn::Expr>()?;
        let content;
        let _ = syn::braced!(content in input);
        let if_true = content.parse()?;
        let _ = input.parse::<syn::Token![else]>()?;
        let content;
        let _ = syn::braced!(content in input);
        let if_false = content.parse()?;
        Ok(Self {
            condition,
            if_true,
            if_false,
        })
    }
}

#[cfg(feature = "nightly")]
#[proc_macro]
pub fn macro_if(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let if_stmt = syn::parse2::<MacroIf>(input).unwrap();

    let condition_tokens: proc_macro::TokenStream = if_stmt.condition.to_token_stream().into();
    let condition = match condition_tokens.expand_expr() {
        Ok(expr) => expr,
        Err(_) => {
            return quote! {
                compile_error!("failed to expand macro_if condition");
            }
            .into();
        }
    };

    let lit_bool = match syn::parse::<syn::LitBool>(condition) {
        Ok(lit_bool) => lit_bool,
        Err(_) => {
            return quote! {
                compile_error!("failed to parse macro_if condition as a boolean literal");
            }
            .into();
        }
    };

    if lit_bool.value {
        if_stmt.if_true.to_token_stream().into()
    } else {
        if_stmt.if_false.to_token_stream().into()
    }
}

#[derive(Clone)]
enum MatchPattern {
    Identifier(syn::Ident),
    Regex(lazy_regex::Regex),
    /// Match on any of the patterns in the vector.
    ///
    /// This pattern expects that the input matches at least one of the patterns in the vector.
    ///
    /// Note that matching on regex patterns is supported,
    /// but if there is different number of capture groups
    /// it is up to the user of the macro to distinguish between them.
    Or(Box<MatchPattern>, Box<MatchPattern>),

    /// Match on a tuple of patterns.
    ///
    /// This pattern expects that the input matches all of the patterns in the tuple.
    Tuple(Vec<MatchPattern>),

    Default,
}

impl std::fmt::Display for MatchPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identifier(ident) => write!(f, "{}", ident),
            Self::Regex(regex) => write!(f, "{}", regex),
            Self::Or(first, second) => write!(f, "{} | {}", first, second),
            Self::Tuple(patterns) => write!(
                f,
                "{}",
                patterns
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::Default => write!(f, "_"),
        }
    }
}

impl Parse for MatchPattern {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let pat = if input.peek(syn::Token![_]) {
            let _ = input.parse::<syn::Token![_]>()?;
            return Ok(Self::Default);
        } else if input.peek(syn::Ident) {
            Self::Identifier(input.parse::<syn::Ident>()?)
        } else if input.peek(syn::LitStr) {
            let lit_str = input.parse::<syn::LitStr>()?;
            let regex = match lazy_regex::Regex::new(&lit_str.value()) {
                Ok(regex) => regex,
                Err(err) => {
                    return Err(syn::Error::new(
                        lit_str.span(),
                        &format!("invalid regex: {}", err),
                    ));
                }
            };
            Self::Regex(regex)
        } else if input.peek(syn::token::Paren) {
            let content;
            let _ = syn::parenthesized!(content in input);
            let patterns: Punctuated<MatchPattern, syn::Token![,]> =
                content.parse_terminated(Self::parse, syn::Token![,])?;
            Self::Tuple(patterns.into_iter().collect())
        } else {
            return Err(input.error("expected identifier, regex, `_`, or tuple pattern"));
        };

        if input.peek(syn::Token![|]) {
            let _ = input.parse::<syn::Token![|]>()?;
            let second = input.parse::<MatchPattern>()?;
            Ok(Self::Or(Box::new(pat), Box::new(second)))
        } else {
            Ok(pat)
        }
    }
}

/// A result of matchin on a pattern
enum MatchResult<'a> {
    /// A single identifier matcched.
    Ident(&'a syn::Ident),
    /// Regex pattern matched, returns the captures.
    Regex(lazy_regex::Captures<'a>),
    /// Tuple pattern matched, returns result for nested patterns.
    Tuple(Vec<MatchResult<'a>>),
    Default,
}

/// A value we match on inside `match_ident!`.
///
/// Current variants are:
/// - `Ident(syn::Ident)`: Match on a single identifier.
/// - `Tuple(Vec<MatchOn>)`: Match on a tuple of values.
enum MatchOn {
    Ident(syn::Ident),
    Tuple(Vec<MatchOn>),
}

impl std::fmt::Display for MatchOn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(ident) => write!(f, "{}", ident),
            Self::Tuple(values) => write!(f, "{}", values.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")),
        }
    }
}

enum MatchReturn<T> {
    NoMatch,
    Single(T),
    Tuple(Vec<Self>),
}

impl MatchPattern {
    pub fn try_match<F, T>(&self, input: &MatchOn, f: &mut F) -> syn::Result<MatchReturn<T>>
    where
        F: FnMut(&MatchResult) -> syn::Result<T>,
    {
        match self {
            Self::Default => f(&MatchResult::Default).map(MatchReturn::Single),
            Self::Identifier(identifier) => match input {
                MatchOn::Ident(ident) => {
                    if ident == identifier {
                        f(&MatchResult::Ident(identifier)).map(MatchReturn::Single)
                    } else {
                        Ok(MatchReturn::NoMatch)
                    }
                }
                _ => Ok(MatchReturn::NoMatch),
            },
            Self::Regex(regex) => match input {
                MatchOn::Ident(ident) => {
                    let s = ident.to_string();
                    if let Some(captures) = regex.captures(&s) {
                        f(&MatchResult::Regex(captures)).map(MatchReturn::Single)
                    } else {
                        Ok(MatchReturn::NoMatch)
                    }
                }
                _ => Ok(MatchReturn::NoMatch),
            },
            Self::Or(first, second) => match first.try_match(input, f)? {
                MatchReturn::NoMatch => second.try_match(input, f),
                result => return Ok(result),
            },

            Self::Tuple(patterns) => match input {
                MatchOn::Ident(_) => Ok(MatchReturn::NoMatch),
                MatchOn::Tuple(values) => {
                    if values.len() != patterns.len() {
                        return Ok(MatchReturn::NoMatch);
                    }
                    let mut results = Vec::with_capacity(patterns.len());
                    for (pattern, value) in patterns.iter().zip(values) {
                        match pattern.try_match(value, f)? {
                            MatchReturn::NoMatch => return Ok(MatchReturn::NoMatch),
                            ret => results.push(ret),
                        }
                    }
                    Ok(MatchReturn::Tuple(results))
                }
            },
        }
    }

    pub fn is_match(&self, input: &MatchOn) -> syn::Result<Option<Self>> {
        match self {
            Self::Default => Ok(Some(self.clone())),
            Self::Identifier(identifier) => match input {
                MatchOn::Ident(ident) if ident == identifier => Ok(Some(self.clone())),
                _ => Ok(None),
            },

            Self::Regex(regex) => match input {
                MatchOn::Ident(ident) => {
                    let s = ident.to_string();
                   
                    if let Some(_c) = regex.captures(&s) {
                        Ok(Some(self.clone()))
                    } else {
                        Ok(None)
                    }
                }
                _ => Ok(None),
            },

            Self::Or(first, second) => match first.is_match(input)? {
                Some(pattern) => Ok(Some(pattern)),
                None => second.is_match(input),
            },

            Self::Tuple(patterns) => match input {
                MatchOn::Tuple(values) => {
                    if values.len() != patterns.len() {
                        return Ok(None);
                    }

                    for (pattern, value) in patterns.iter().zip(values) {
                        if pattern.is_match(value)?.is_none() {
                            return Ok(None);
                        }
                    }
                    Ok(Some(self.clone()))
                }
                _ => Ok(None),
            },
        }
    }
}

impl Parse for MatchOn {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(syn::Ident) {
            Ok(Self::Ident(input.parse::<syn::Ident>()?))
        } else {
            let content;
            let _ = syn::parenthesized!(content in input);
            let idents: Punctuated<MatchOn, syn::Token![,]> =
                content.parse_terminated(Self::parse, syn::Token![,])?;
            Ok(Self::Tuple(idents.into_iter().collect()))
        }
    }
}

struct Matches {
    value: MatchOn,
    pattern: MatchPattern,
}

impl Parse for Matches {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let value = input.parse::<MatchOn>()?;
        let _ = input.parse::<syn::Token![,]>()?;
        let pattern = input.parse::<MatchPattern>()?;
        println!("pattern: {}", pattern);
        Ok(Self { value, pattern })
    }
}

#[proc_macro]
pub fn ident_matches(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let Matches { value, pattern } = match syn::parse::<Matches>(input) {
        Ok(matches) => matches,
        Err(err) => {
            return err.to_compile_error().into();
        }
    };

    match pattern.try_match(&value, &mut |_| Ok(())) {
        Err(err) => return err.to_compile_error().into(),
        Ok(MatchReturn::Single(_)) => quote! { true }.into(),
        Ok(MatchReturn::NoMatch) => quote! { false }.into(),
        Ok(MatchReturn::Tuple(_)) => quote! { true }.into(),
    }
}

fn paste_captures(
    input: TokenStream,
    captures: &lazy_regex::Captures<'_>,
) -> syn::Result<TokenStream> {
    let mut tokens = input.clone().into_iter().peekable();
    let mut output = TokenStream::new();
    loop {
        match &tokens.peek() {
            Some(TokenTree::Punct(punct)) if punct.as_char() == '@' => {
                let punct = tokens.next().unwrap();
                if let Some(TokenTree::Literal(lit)) = tokens.peek() {
                    if let Lit::Int(intliut) = Lit::new(lit.clone()) {
                        if let Ok(num) = intliut.base10_parse::<usize>() {
                            tokens.next().unwrap();

                            if let Some(capture) = captures.get(num) {
                                let s = capture.as_str();
                                output.extend(quote! {
                                    #s
                                });
                                continue;
                            } else {
                                return Err(syn::Error::new(
                                    punct.span(),
                                    &format!("capture group index out of bounds: {}", num),
                                ));
                            }
                        }
                    }
                } else if let Some(TokenTree::Ident(name)) = tokens.peek() {
                    if let Some(capture) = captures.name(&name.to_string()) {
                        tokens.next().unwrap();
                        let s = capture.as_str();
                        output.extend(quote! {
                            #s
                        });
                        continue;
                    }
                }
                output.extend(std::iter::once(punct));
            }

            Some(TokenTree::Punct(punct)) if punct.as_char() == '$' => {
                let punct = tokens.next().unwrap();
                if let Some(TokenTree::Literal(lit)) = tokens.peek() {
                    if let Lit::Int(intliut) = Lit::new(lit.clone()) {
                        if let Ok(num) = intliut.base10_parse::<usize>() {
                            tokens.next().unwrap();

                            if let Some(capture) = captures.get(num) {
                                let s = Ident::new(capture.as_str(), punct.span());
                                output.extend(quote! {
                                    #s
                                });
                                continue;
                            } else {
                                return Err(syn::Error::new(
                                    punct.span(),
                                    &format!("capture group index out of bounds: {}", num),
                                ));
                            }
                        }
                    }
                } else if let Some(TokenTree::Ident(name)) = tokens.peek() {
                    if let Some(match_) = captures.name(&name.to_string()) {
                        tokens.next().unwrap();
                        let s = Ident::new(match_.as_str(), punct.span());
                        output.extend(quote! {
                            #s
                        });
                        continue;
                    }
                }

                output.extend(std::iter::once(punct));
            }

            Some(TokenTree::Group(_)) => {
                let TokenTree::Group(group) = tokens.next().unwrap() else {
                    unreachable!()
                };
                let delim = group.delimiter();
                let span = group.span();
                let expanded = paste_captures(group.stream(), captures)?;
                let mut group = Group::new(delim, expanded);
                group.set_span(span);
                output.extend(std::iter::once(TokenTree::Group(group)));
            }

            Some(_) => {
                let token = tokens.next().unwrap();
                output.extend(std::iter::once(token));
            }

            _ => {
                break;
            }
        }
    }

    Ok(output)
}

struct MatchArm {
    pattern: MatchPattern,
    body: TokenStream,
}

impl Parse for MatchArm {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let pattern = input.parse::<MatchPattern>()?;
        let _ = input.parse::<syn::Token![=>]>()?;
        let body;
        let _ = syn::braced!(body in input);
        let body = body.parse::<TokenStream>()?;
        Ok(Self { pattern, body })
    }
}

impl std::fmt::Display for MatchArm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} => {}", self.pattern, self.body)
    }
}

struct MatchIdent {
    value: MatchOn,
    arms: Vec<MatchArm>,
}

impl Parse for MatchIdent {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _ = input.parse::<syn::Token![match]>()?;
        let value = input.parse::<MatchOn>()?;
        let content;
        let _ = syn::braced!(content in input);

        let arms = content.parse_terminated(MatchArm::parse, syn::Token![,])?;

        Ok(Self {
            value,
            arms: arms.into_iter().collect(),
        })
    }
}

impl MatchPattern {
    pub fn expand(&self, body: TokenStream, match_on: &MatchOn) -> syn::Result<TokenStream> {
        match self {
            Self::Default => Ok(body),
            Self::Identifier(_) => Ok(body),

            Self::Regex(regex) => match match_on {
                MatchOn::Ident(ident) => paste_captures(
                    body.clone(),
                    &regex
                        .captures(&ident.to_string())
                        .ok_or_else(|| syn::Error::new(body.span(), "regex did not match"))?,
                ),

                _ => unreachable!(),
            },

            Self::Or(_, _) => {
                unreachable!("Or patterns should be removed by `is_match`")
            }

            Self::Tuple(patterns) => match match_on {
                MatchOn::Ident(_) => unreachable!(),
                MatchOn::Tuple(values) => {
                    let mut body = body;
                    for (pattern, value) in patterns.iter().zip(values) {
                        body = pattern.expand(body, value)?;
                    }
                    Ok(body)
                }
            },
        }
    }
}

#[proc_macro]
pub fn match_ident(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let match_ident = match syn::parse::<MatchIdent>(input) {
        Ok(match_ident) => match_ident,
        Err(err) => return err.to_compile_error().into(),
    };

    let value = match_ident.value;
    let arms = match_ident.arms;

    for arm in arms {
        match arm.pattern.is_match(&value) {
            Ok(Some(pattern)) => match pattern.expand(arm.body, &value) {
                Ok(expanded) => {
                    return expanded.into();
                }
                Err(err) => return err.to_compile_error().into(),
            },

            Ok(None) => continue,
            Err(err) => return err.to_compile_error().into(),
        }
    }
    quote! {}.into()
}
