use crate::fmt::Fmt;

pub struct Stream {
    state: u64,
}

impl Stream {
    pub fn new(seed: u64) -> Stream {
        Stream { state: seed }
    }

    pub fn draw(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn whole(&mut self, f: Fmt) -> u64 {
        loop {
            let u = self.draw();
            let bits = match f {
                Fmt::F64 => u,
                Fmt::F32 => u & 0xFFFF_FFFF,
            };
            if !f.is_nan(bits) {
                return bits;
            }
        }
    }

    pub fn range(&mut self, f: Fmt, lo: u64, hi: u64, signed: bool) -> u64 {
        let u = self.draw();
        let magnitude = lo + (u % (1 << 63)) % (hi - lo + 1);
        if signed && u >> 63 == 1 {
            magnitude | f.sign()
        } else {
            magnitude
        }
    }
}
