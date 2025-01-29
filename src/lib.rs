#![feature(proc_macro_expand)]
use lazy_regex::Captures;
use proc_macro2::{Group, Literal, Span, TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
    spanned::Spanned,
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

enum MatchPattern {
    Identifier(syn::Ident),
    Regex(lazy_regex::Regex),
    Default,
}

impl Parse for MatchPattern {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(syn::Token![_]) {
            return Ok(Self::Default);
        }

        if input.peek(syn::Ident) {
            let ident = input.parse::<syn::Ident>()?;
            Ok(Self::Identifier(ident))
        } else {
            let regex = input.parse::<syn::LitStr>()?;
            let regex = match lazy_regex::Regex::new(&regex.value()) {
                Ok(regex) => regex,
                Err(err) => {
                    return Err(syn::Error::new(
                        regex.span(),
                        &format!("invalid regex: {}", err),
                    ));
                }
            };
            Ok(Self::Regex(regex))
        }
    }
}

struct MatchIdent {
    pub match_on: syn::Ident,
    pub expr_mode: bool,
    pub body: Punctuated<(MatchPattern, proc_macro2::TokenStream), syn::Token![,]>,
}

mod kw {
    syn::custom_keyword!(expr);
}

impl Parse for MatchIdent {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _ = input.parse::<syn::Token![match]>()?;

        let expr_mode = if input.peek(kw::expr) {
            input.parse::<kw::expr>()?;
            true
        } else {
            false
        };

        let match_on = input.parse::<_>()?;
        let content;
        let _ = syn::braced!(content in input);

        let body = content.parse_terminated(
            |input| {
                let pattern = input.parse::<MatchPattern>()?;
                let _ = input.parse::<syn::Token![=>]>()?;
                let content;
                let _ = syn::braced!(content in input);
                let branch = content.parse::<proc_macro2::TokenStream>()?;
                Ok((pattern, branch))
            },
            syn::Token![,],
        )?;

        Ok(Self {
            match_on,
            body,
            expr_mode,
        })
    }
}

/// Match on an identifier and expand into corresponding branch.
///
/// ```rust
/// ident_match! {
///     match $id {
///         foo => {
///             println!("foo");
///         }
///         bar => {
///             println!("bar");
///         }
///
///         r#"b(ar)"# => {
///             println!("bar");
///         }
///     }
/// }
/// ```
#[proc_macro]
pub fn ident_match(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let match_stmt = syn::parse2::<MatchIdent>(input).unwrap();

    let match_on_str = match_stmt.match_on.to_string();
    let match_on = &match_stmt.match_on;

    for (pattern, branch) in match_stmt.body {
        match pattern {
            MatchPattern::Identifier(ident) => {
                if ident == *match_on {
                    return branch.into();
                }
            }

            MatchPattern::Regex(regex) => {
                let captures = regex.captures(&match_on_str);
                if let Some(captures) = captures {
                    let branch = match expand_paste_capture_group(
                        branch.clone(),
                        branch.span(),
                        &captures,
                    ) {
                        Ok(branch) => branch,
                        Err(err) => {
                            return err.to_compile_error().into();
                        }
                    };
                    return branch.into();
                }
            }

            MatchPattern::Default => {
                return branch.into();
            }
        }
    }

    TokenStream::new().into()
}

fn expand_paste_capture_group(
    input: TokenStream,
    _scope: Span,
    captures: &Captures<'_>,
) -> syn::Result<TokenStream> {
    let mut expanded = TokenStream::new();
    let mut tokens = input.clone().into_iter().peekable();

    loop {
        println!("expand loop {:?}", tokens.peek());
        let span = input.span();
        if let Some(num) = is_paste_capture_group_str(input.clone(), span.clone())? {
            println!("is_paste_capture_group_str");
            tokens.next().unwrap();
            tokens.next().unwrap();
            let capture = captures.get(num).ok_or_else(|| {
                syn::Error::new(span, &format!("capture group index out of bounds: {}", num))
            })?;
            expanded.extend(std::iter::once(TokenTree::Literal(Literal::string(
                capture.as_str(),
            ))));
            continue;
        } else if let Some(num) = is_paste_capture_group_ident(input.clone(), span.clone())? {
            tokens.next().unwrap();
            tokens.next().unwrap();
            let capture = captures.get(num).ok_or_else(|| {
                syn::Error::new(span, &format!("capture group index out of bounds: {}", num))
            })?;
            let id = proc_macro2::Ident::new(capture.as_str(), span);
            expanded.extend(std::iter::once(TokenTree::Ident(id)));
            continue;
        }

        let token = tokens.next();

        match token {
            Some(TokenTree::Group(group)) => {
                let delimiter = group.delimiter();
                let content = group.stream();
                let span = group.span();
                
                let nested = expand_paste_capture_group(content, span, captures)?;
                println!("expand nested {}", nested);
                let mut group = Group::new(delimiter, nested);
                group.set_span(span);
                expanded.extend(group.stream());
            }

            Some(token) => {
                expanded.extend(std::iter::once(token));
            }

            None => {
                break;
            }
        }
    }

    Ok(expanded)
}

fn is_paste_capture_group_str(input: TokenStream, _scope: Span) -> syn::Result<Option<usize>> {
    let mut tokens = input.clone().into_iter();
    println!("check {}", input);
    match &tokens.next() {
        Some(TokenTree::Punct(punct)) if punct.as_char() == '$' => {
            println!("is_paste_capture_group_str $");
        }

        _ => return Ok(None),
    }

    match &tokens.next() {
        Some(TokenTree::Literal(lit)) => {
            let syn_lit = syn::Lit::new(lit.clone());
            if let syn::Lit::Int(integer) = syn_lit {
                let num = integer.base10_parse::<usize>().unwrap();
                return Ok(Some(num));
            }

            return Ok(None);
        }

        _ => return Ok(None),
    }
}

fn is_paste_capture_group_ident(input: TokenStream, _scope: Span) -> syn::Result<Option<usize>> {
    let mut tokens = input.clone().into_iter();

    match &tokens.next() {
        Some(TokenTree::Punct(punct)) if punct.as_char() == '@' => {}

        _ => return Ok(None),
    }

    match &tokens.next() {
        Some(TokenTree::Literal(lit)) => {
            let syn_lit = syn::Lit::new(lit.clone());
            if let syn::Lit::Int(integer) = syn_lit {
                let num = integer.base10_parse::<usize>().unwrap();
                return Ok(Some(num));
            }

            return Ok(None);
        }

        _ => return Ok(None),
    }
}
