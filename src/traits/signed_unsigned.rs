trait Signed {
    type Unsigned: Unsigned;
}

trait Unsigned {
    type Signed: Signed;
}

macro_rules! pair {
    ($uty:ty, $ity:ty) => {
        impl Unsigned for $uty {
            type Signed = $ity;
        }

        impl Signed for $ity {
            type Unsigned = $uty;
        }
    }
}

pair!(u8, i8);
pair!(u16, i16);
pair!(u32, i32);
pair!(u64, i64);
pair!(u128, i128);
