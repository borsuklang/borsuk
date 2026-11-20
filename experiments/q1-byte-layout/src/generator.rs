use crate::types::{
    CommandId, ConfirmIn, Corpus, Flag, HoldIn, Kind, N, PersonIn, Varied, VariedIn, Wide, WideIn,
    hold_token,
};

pub const SEED: u64 = 0x5EED;

const YEAR_START: u64 = 1_767_225_600_000_000_000;

const YEAR_END: u64 = 1_798_761_600_000_000_000;

const INT_CLASSES: [(u64, u64, u64); 6] = [
    (16, 0, 1 << 7),
    (42, 1 << 7, 1 << 14),
    (61, 1 << 14, 1 << 21),
    (80, 1 << 21, 1 << 28),
    (92, 1 << 28, 1 << 35),
    (100, 1 << 49, 1 << 56),
];

const TEXT_CLASSES: [(u64, u64, u64); 7] = [
    (338, 0, 8),
    (491, 9, 16),
    (567, 17, 22),
    (702, 23, 32),
    (808, 33, 64),
    (869, 65, 128),
    (949, 129, 512),
];

const NAME_CLASSES: [(u64, u64, u64); 3] = [(80, 10, 28), (95, 29, 31), (100, 32, 60)];

const MONEY_CLASSES: [(u64, u64); 3] = [(50, 500), (500, 5000), (5000, 50000)];

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

    fn below(&mut self, a: u64, b: u64) -> u64 {
        a + self.draw() % (b - a)
    }

    fn within(&mut self, a: u64, b: u64) -> u64 {
        a + self.draw() % (b - a + 1)
    }

    fn class(&mut self, modulus: u64, classes: &[(u64, u64, u64)]) -> (u64, u64) {
        let u = self.draw() % modulus;
        let i = classes
            .iter()
            .take_while(|(limit, _, _)| u >= *limit)
            .count();
        (classes[i].1, classes[i].2)
    }

    fn time(&mut self) -> i64 {
        self.below(YEAR_START, YEAR_END) as i64
    }

    fn int(&mut self) -> i64 {
        let (a, b) = self.class(100, &INT_CLASSES);
        let magnitude = self.below(a, b) as i64;
        if self.draw() % 100 < 2 {
            -magnitude
        } else {
            magnitude
        }
    }

    fn letters(&mut self, len: u64) -> String {
        (0..len)
            .map(|_| char::from(b'a' + (self.draw() % 26) as u8))
            .collect()
    }

    fn digits(&mut self, len: u64) -> String {
        (0..len)
            .map(|_| char::from(b'0' + (self.draw() % 10) as u8))
            .collect()
    }

    fn text(&mut self) -> String {
        let (a, b) = self.class(949, &TEXT_CLASSES);
        let len = self.within(a, b);
        self.letters(len)
    }

    fn principal(&mut self) -> String {
        let (a, b) = self.class(100, &NAME_CLASSES);
        let len = self.within(a, b);
        self.letters(len)
    }

    fn command(&mut self) -> CommandId {
        let mut bytes = [0u8; 34];
        bytes[0..2].copy_from_slice(&1u16.to_le_bytes());
        bytes[2..10].copy_from_slice(&self.below(0, 1 << 32).to_le_bytes());
        bytes[10..18].copy_from_slice(&self.time().to_le_bytes());
        bytes[18..26].copy_from_slice(&self.draw().to_le_bytes());
        bytes[26..34].copy_from_slice(&self.draw().to_le_bytes());
        CommandId(bytes)
    }

    fn flag(&mut self) -> Flag {
        match self.draw() % 4 {
            0 => Flag::A,
            1 => Flag::B,
            2 => Flag::C,
            _ => Flag::D,
        }
    }

    fn boolean(&mut self) -> bool {
        self.draw() % 100 < 50
    }

    fn float(&mut self) -> u64 {
        ((self.draw() % 100_000) as f64 / 100.0).to_bits()
    }

    fn money(&mut self) -> i128 {
        let (a, b) = MONEY_CLASSES[(self.draw() % 3) as usize];
        i128::from(self.below(a, b))
    }

    fn kind(&mut self) -> Kind {
        match self.draw() % 3 {
            0 => Kind::Plain,
            1 => Kind::Tagged(self.text()),
            _ => {
                let a = self.int();
                let b = self.int();
                Kind::Scored(a, b)
            }
        }
    }

    fn hold(&mut self) -> HoldIn {
        let cmd = self.command();
        let key = self.below(0, 1 << 32) as i64;
        let sender = self.principal();
        let now = self.time();
        HoldIn {
            cmd,
            key,
            sender,
            now,
        }
    }

    fn wide(&mut self) -> WideIn {
        let cmd = self.command();
        let ints = std::array::from_fn(|_| self.int());
        let flags = std::array::from_fn(|_| self.flag());
        let bools = std::array::from_fn(|_| self.boolean());
        let floats = std::array::from_fn(|_| self.float());
        let money = self.money();
        WideIn {
            cmd,
            wide: Wide {
                ints,
                flags,
                bools,
                floats,
                money,
            },
        }
    }

    fn varied(&mut self) -> VariedIn {
        let cmd = self.command();
        let texts = std::array::from_fn(|_| self.text());
        let opt = if self.draw() % 100 < 50 {
            Some(self.text())
        } else {
            None
        };
        let res = if self.draw() % 100 < 70 {
            Ok(self.int())
        } else {
            Err(self.text())
        };
        let kind = self.kind();
        let ints = std::array::from_fn(|_| self.int());
        VariedIn {
            cmd,
            varied: Varied {
                texts,
                opt,
                res,
                kind,
                ints,
            },
        }
    }

    fn person(&mut self) -> PersonIn {
        let cmd = self.command();
        let id = self.int();
        let name_len = self.within(5, 39);
        let name = self.letters(name_len);
        let email = self.principal();
        let phone_len = self.within(8, 15);
        let phone = self.digits(phone_len);
        let visits = self.int();
        let score = self.int();
        let since = self.time();
        PersonIn {
            cmd,
            id,
            name,
            email,
            phone,
            visits,
            score,
            since,
        }
    }
}

pub fn corpus() -> Corpus {
    let mut s = Stream::new(SEED);
    let mut pad = [0u8; 128];
    for chunk in pad.chunks_mut(8) {
        chunk.copy_from_slice(&s.draw().to_le_bytes());
    }
    let mut hold = Vec::with_capacity(N);
    let mut confirm_parts = Vec::with_capacity(N);
    for _ in 0..N {
        hold.push(s.hold());
        let cmd = s.command();
        let now = s.time();
        confirm_parts.push((cmd, now));
    }
    let wide = (0..N).map(|_| s.wide()).collect();
    let varied = (0..N).map(|_| s.varied()).collect();
    let person = (0..N).map(|_| s.person()).collect();
    let mut corpus = Corpus {
        pad,
        hold,
        confirm: Vec::with_capacity(N),
        wide,
        varied,
        person,
    };
    for (i, (cmd, now)) in confirm_parts.into_iter().enumerate() {
        let token = hold_token(&corpus, i);
        let h = &corpus.hold[i];
        let confirm = ConfirmIn {
            cmd,
            key: h.key,
            sender: h.sender.clone(),
            now,
            token,
        };
        corpus.confirm.push(confirm);
    }
    corpus
}
