use macro_extra::{ident_matches, match_ident};

macro_rules! check {
    ($($n: ident),*) => {
        match_ident! {
            match ($($n),*) {
                (dst, lhs, rhs) => {
                    println!("dst lhs rhs");
                },

                _ => {
                    println!("other");
                }
            }
        }
    };
}

fn main() {
    check!(
        dst, lhs, rhs
    );

    check!(
        src_dst
    );
}
