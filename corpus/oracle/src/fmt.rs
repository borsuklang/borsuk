#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Fmt {
    F64,
    F32,
}

pub const FORMATS: [Fmt; 2] = [Fmt::F64, Fmt::F32];

impl Fmt {
    pub fn prec(self) -> u32 {
        match self {
            Fmt::F64 => 53,
            Fmt::F32 => 24,
        }
    }

    pub fn emax(self) -> i32 {
        match self {
            Fmt::F64 => 1023,
            Fmt::F32 => 127,
        }
    }

    pub fn width(self) -> u32 {
        match self {
            Fmt::F64 => 64,
            Fmt::F32 => 32,
        }
    }

    pub fn sign(self) -> u64 {
        1 << (self.width() - 1)
    }

    pub fn exponent_mask(self) -> u64 {
        match self {
            Fmt::F64 => 0x7FF0_0000_0000_0000,
            Fmt::F32 => 0x7F80_0000,
        }
    }

    pub fn nan(self) -> u64 {
        match self {
            Fmt::F64 => 0x7FF8_0000_0000_0000,
            Fmt::F32 => 0x7FC0_0000,
        }
    }

    pub fn is_nan(self, bits: u64) -> bool {
        let magnitude = bits & !self.sign();
        magnitude > self.exponent_mask()
    }

    pub fn name(self) -> &'static str {
        match self {
            Fmt::F64 => "f64",
            Fmt::F32 => "f32",
        }
    }

    pub fn ty(self) -> &'static str {
        match self {
            Fmt::F64 => "F64",
            Fmt::F32 => "F32",
        }
    }
}
