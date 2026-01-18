//! Arm64 opcode classification
//!
//! Single source of truth for Arm64 opcode classification used by both
//! the verifier (binary) and instrumenter (text assembly).

use std::collections::HashMap;

use lazy_static::lazy_static;
use yaxpeax_arm::armv8::a64::Opcode;

/// Result of checking an instruction against the whitelist
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
pub enum CheckResult {
    /// Instruction is allowed
    Allowed,
    /// Instruction is rejected with a reason
    Rejected(RejectionReason),
}

/// Reason an instruction was rejected
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
pub enum RejectionReason {
    /// Atomic/exclusive instruction (non-deterministic monitor state)
    Atomic,
    /// System instruction (privileged operation)
    System,
    /// Memory barrier (affects ordering non-deterministically)
    Barrier,
    /// Floating-point instruction (implementation-defined precision)
    FloatingPoint,
    /// Indirect branch (unverifiable target, requires rewriting)
    IndirectBranch,
    /// Pointer authentication (depends on system keys)
    PointerAuth,
    /// Memory tagging extension (depends on system state)
    MemoryTagging,
    /// Unknown/invalid instruction (not in whitelist)
    Unknown,
}

impl std::fmt::Display for RejectionReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RejectionReason::Atomic => write!(f, "atomic/exclusive instruction"),
            RejectionReason::System => write!(f, "system instruction"),
            RejectionReason::Barrier => write!(f, "memory barrier"),
            RejectionReason::FloatingPoint => write!(f, "floating-point instruction"),
            RejectionReason::IndirectBranch => write!(f, "indirect branch (requires rewriting)"),
            RejectionReason::PointerAuth => write!(f, "pointer authentication instruction"),
            RejectionReason::MemoryTagging => write!(f, "memory tagging instruction"),
            RejectionReason::Unknown => write!(f, "unknown instruction"),
        }
    }
}

/// Classification of an Arm64 opcode
pub struct ClassifiedOpcode {
    /// The mnemonic string (e.g., "add", "b.eq")
    pub mnemonic: &'static str,
    /// Control flow: is this a branch instruction?
    pub is_branch: bool,
    /// Control flow: is this a call? (BL, BLR, BLRAA, etc.)
    pub is_call: bool,
    /// Control flow: is this a return? (RET, RETAA, etc.)
    pub is_return: bool,
    /// Control flow: does this have an indirect (register) target?
    pub is_indirect: bool,
    /// Control flow: can this instruction fall through? (conditional branches)
    pub is_conditional: bool,
    /// Verification result
    pub check_result: CheckResult,
}

impl ClassifiedOpcode {
    const fn allowed(mnemonic: &'static str) -> Self {
        Self {
            mnemonic,
            is_branch: false,
            is_call: false,
            is_return: false,
            is_indirect: false,
            is_conditional: false,
            check_result: CheckResult::Allowed,
        }
    }

    const fn rejected(mnemonic: &'static str, reason: RejectionReason) -> Self {
        Self {
            mnemonic,
            is_branch: false,
            is_call: false,
            is_return: false,
            is_indirect: false,
            is_conditional: false,
            check_result: CheckResult::Rejected(reason),
        }
    }

    const fn direct_branch(mnemonic: &'static str) -> Self {
        Self {
            mnemonic,
            is_branch: true,
            is_call: false,
            is_return: false,
            is_indirect: false,
            is_conditional: false,
            check_result: CheckResult::Allowed,
        }
    }

    const fn direct_call(mnemonic: &'static str) -> Self {
        Self {
            mnemonic,
            is_branch: true,
            is_call: true,
            is_return: false,
            is_indirect: false,
            is_conditional: false,
            check_result: CheckResult::Allowed,
        }
    }

    const fn conditional_branch(mnemonic: &'static str) -> Self {
        Self {
            mnemonic,
            is_branch: true,
            is_call: false,
            is_return: false,
            is_indirect: false,
            is_conditional: true,
            check_result: CheckResult::Allowed,
        }
    }

    const fn indirect_branch(mnemonic: &'static str) -> Self {
        Self {
            mnemonic,
            is_branch: true,
            is_call: false,
            is_return: false,
            is_indirect: true,
            is_conditional: false,
            check_result: CheckResult::Rejected(RejectionReason::IndirectBranch),
        }
    }

    const fn indirect_call(mnemonic: &'static str) -> Self {
        Self {
            mnemonic,
            is_branch: true,
            is_call: true,
            is_return: false,
            is_indirect: true,
            is_conditional: false,
            check_result: CheckResult::Rejected(RejectionReason::IndirectBranch),
        }
    }

    const fn indirect_return(mnemonic: &'static str) -> Self {
        Self {
            mnemonic,
            is_branch: true,
            is_call: false,
            is_return: true,
            is_indirect: true,
            is_conditional: false,
            check_result: CheckResult::Rejected(RejectionReason::IndirectBranch),
        }
    }

    /// Unknown opcode classification (returned for opcodes not in the map)
    pub const UNKNOWN: Self = Self {
        mnemonic: "unknown",
        is_branch: false,
        is_call: false,
        is_return: false,
        is_indirect: false,
        is_conditional: false,
        check_result: CheckResult::Rejected(RejectionReason::Unknown),
    };

    /// Classify an opcode (for native-verifier)
    ///
    /// Converts the opcode to its mnemonic string and looks up in the map.
    /// Returns UNKNOWN for opcodes not in the map.
    pub fn from_opcode(op: Opcode) -> &'static Self {
        let mnemonic = op.to_string();
        BY_MNEMONIC
            .get(mnemonic.as_str())
            .copied()
            .unwrap_or(&Self::UNKNOWN)
    }

    /// Classify by mnemonic string (for gas-instrument)
    ///
    /// Returns None for unknown mnemonics.
    pub fn from_mnemonic(mnemonic: &str) -> Option<&'static Self> {
        BY_MNEMONIC
            .get(mnemonic.to_ascii_lowercase().as_str())
            .copied()
    }
}

/// Single source of truth: all classified opcodes
const OPCODE_TABLE: &[ClassifiedOpcode] = &[
    // Allowed: Base integer arithmetic
    ClassifiedOpcode::allowed("add"),
    ClassifiedOpcode::allowed("adds"),
    ClassifiedOpcode::allowed("sub"),
    ClassifiedOpcode::allowed("subs"),
    ClassifiedOpcode::allowed("cmp"),
    ClassifiedOpcode::allowed("cmn"),
    ClassifiedOpcode::allowed("adc"),
    ClassifiedOpcode::allowed("adcs"),
    ClassifiedOpcode::allowed("sbc"),
    ClassifiedOpcode::allowed("sbcs"),
    ClassifiedOpcode::allowed("neg"),
    ClassifiedOpcode::allowed("negs"),
    // Multiply/divide
    ClassifiedOpcode::allowed("madd"),
    ClassifiedOpcode::allowed("msub"),
    ClassifiedOpcode::allowed("smaddl"),
    ClassifiedOpcode::allowed("smsubl"),
    ClassifiedOpcode::allowed("smulh"),
    ClassifiedOpcode::allowed("umaddl"),
    ClassifiedOpcode::allowed("umsubl"),
    ClassifiedOpcode::allowed("umulh"),
    ClassifiedOpcode::allowed("udiv"),
    ClassifiedOpcode::allowed("sdiv"),
    ClassifiedOpcode::allowed("mul"),
    // Allowed: Logic operations
    ClassifiedOpcode::allowed("and"),
    ClassifiedOpcode::allowed("ands"),
    ClassifiedOpcode::allowed("tst"),
    ClassifiedOpcode::allowed("orr"),
    ClassifiedOpcode::allowed("orn"),
    ClassifiedOpcode::allowed("eor"),
    ClassifiedOpcode::allowed("eon"),
    ClassifiedOpcode::allowed("bic"),
    ClassifiedOpcode::allowed("bics"),
    ClassifiedOpcode::allowed("mvn"),
    // Allowed: Move instructions
    ClassifiedOpcode::allowed("movn"),
    ClassifiedOpcode::allowed("movk"),
    ClassifiedOpcode::allowed("movz"),
    // Allowed: Bit manipulation
    ClassifiedOpcode::allowed("bfm"),
    ClassifiedOpcode::allowed("ubfm"),
    ClassifiedOpcode::allowed("sbfm"),
    ClassifiedOpcode::allowed("extr"),
    ClassifiedOpcode::allowed("rbit"),
    ClassifiedOpcode::allowed("rev"),
    ClassifiedOpcode::allowed("rev16"),
    ClassifiedOpcode::allowed("rev32"),
    ClassifiedOpcode::allowed("rev64"),
    ClassifiedOpcode::allowed("clz"),
    ClassifiedOpcode::allowed("cls"),
    // Allowed: Shifts
    ClassifiedOpcode::allowed("lslv"),
    ClassifiedOpcode::allowed("lsrv"),
    ClassifiedOpcode::allowed("asrv"),
    ClassifiedOpcode::allowed("rorv"),
    // Allowed: Address generation
    ClassifiedOpcode::allowed("adr"),
    ClassifiedOpcode::allowed("adrp"),
    // Allowed: Non-exclusive loads
    ClassifiedOpcode::allowed("ldp"),
    ClassifiedOpcode::allowed("ldpsw"),
    ClassifiedOpcode::allowed("ldr"),
    ClassifiedOpcode::allowed("ldrb"),
    ClassifiedOpcode::allowed("ldrsb"),
    ClassifiedOpcode::allowed("ldrsw"),
    ClassifiedOpcode::allowed("ldrsh"),
    ClassifiedOpcode::allowed("ldrh"),
    ClassifiedOpcode::allowed("ldtr"),
    ClassifiedOpcode::allowed("ldtrb"),
    ClassifiedOpcode::allowed("ldtrh"),
    ClassifiedOpcode::allowed("ldtrsb"),
    ClassifiedOpcode::allowed("ldtrsh"),
    ClassifiedOpcode::allowed("ldtrsw"),
    ClassifiedOpcode::allowed("ldur"),
    ClassifiedOpcode::allowed("ldurb"),
    ClassifiedOpcode::allowed("ldursb"),
    ClassifiedOpcode::allowed("ldursw"),
    ClassifiedOpcode::allowed("ldursh"),
    ClassifiedOpcode::allowed("ldurh"),
    ClassifiedOpcode::allowed("ldnp"),
    // Allowed: Non-exclusive stores
    ClassifiedOpcode::allowed("stp"),
    ClassifiedOpcode::allowed("str"),
    ClassifiedOpcode::allowed("strw"),
    ClassifiedOpcode::allowed("strb"),
    ClassifiedOpcode::allowed("strh"),
    ClassifiedOpcode::allowed("sttr"),
    ClassifiedOpcode::allowed("sttrb"),
    ClassifiedOpcode::allowed("sttrh"),
    ClassifiedOpcode::allowed("stur"),
    ClassifiedOpcode::allowed("sturb"),
    ClassifiedOpcode::allowed("sturh"),
    ClassifiedOpcode::allowed("stnp"),
    // Allowed: Direct branches
    ClassifiedOpcode::direct_branch("b"),
    ClassifiedOpcode::direct_call("bl"),
    // Conditional branches - all 16 conditions
    ClassifiedOpcode::conditional_branch("b.eq"),
    ClassifiedOpcode::conditional_branch("b.ne"),
    ClassifiedOpcode::conditional_branch("b.hs"),
    ClassifiedOpcode::conditional_branch("b.lo"),
    ClassifiedOpcode::conditional_branch("b.mi"),
    ClassifiedOpcode::conditional_branch("b.pl"),
    ClassifiedOpcode::conditional_branch("b.vs"),
    ClassifiedOpcode::conditional_branch("b.vc"),
    ClassifiedOpcode::conditional_branch("b.hi"),
    ClassifiedOpcode::conditional_branch("b.ls"),
    ClassifiedOpcode::conditional_branch("b.ge"),
    ClassifiedOpcode::conditional_branch("b.lt"),
    ClassifiedOpcode::conditional_branch("b.gt"),
    ClassifiedOpcode::conditional_branch("b.le"),
    ClassifiedOpcode::conditional_branch("b.al"),
    ClassifiedOpcode::conditional_branch("b.nv"),
    // BCcc (branch consistent conditional) - same conditions
    ClassifiedOpcode::conditional_branch("bc.eq"),
    ClassifiedOpcode::conditional_branch("bc.ne"),
    ClassifiedOpcode::conditional_branch("bc.hs"),
    ClassifiedOpcode::conditional_branch("bc.lo"),
    ClassifiedOpcode::conditional_branch("bc.mi"),
    ClassifiedOpcode::conditional_branch("bc.pl"),
    ClassifiedOpcode::conditional_branch("bc.vs"),
    ClassifiedOpcode::conditional_branch("bc.vc"),
    ClassifiedOpcode::conditional_branch("bc.hi"),
    ClassifiedOpcode::conditional_branch("bc.ls"),
    ClassifiedOpcode::conditional_branch("bc.ge"),
    ClassifiedOpcode::conditional_branch("bc.lt"),
    ClassifiedOpcode::conditional_branch("bc.gt"),
    ClassifiedOpcode::conditional_branch("bc.le"),
    ClassifiedOpcode::conditional_branch("bc.al"),
    ClassifiedOpcode::conditional_branch("bc.nv"),
    // Compare and branch
    ClassifiedOpcode::conditional_branch("tbz"),
    ClassifiedOpcode::conditional_branch("tbnz"),
    ClassifiedOpcode::conditional_branch("cbz"),
    ClassifiedOpcode::conditional_branch("cbnz"),
    // Allowed: Conditional select/compare
    ClassifiedOpcode::allowed("csel"),
    ClassifiedOpcode::allowed("csneg"),
    ClassifiedOpcode::allowed("csinc"),
    ClassifiedOpcode::allowed("csinv"),
    ClassifiedOpcode::allowed("ccmn"),
    ClassifiedOpcode::allowed("ccmp"),
    // Allowed: CRC (deterministic)
    ClassifiedOpcode::allowed("crc32b"),
    ClassifiedOpcode::allowed("crc32h"),
    ClassifiedOpcode::allowed("crc32w"),
    ClassifiedOpcode::allowed("crc32x"),
    ClassifiedOpcode::allowed("crc32cb"),
    ClassifiedOpcode::allowed("crc32ch"),
    ClassifiedOpcode::allowed("crc32cw"),
    ClassifiedOpcode::allowed("crc32cx"),
    // Allowed: Hints and special
    ClassifiedOpcode::allowed("hint"),
    ClassifiedOpcode::allowed("nop"),
    ClassifiedOpcode::allowed("brk"), // For gas trap
    ClassifiedOpcode::allowed("udf"), // Explicit undefined
    // Prefetch (no side effects)
    ClassifiedOpcode::allowed("prfm"),
    ClassifiedOpcode::allowed("prfum"),
    // Allowed: SIMD vector loads/stores
    ClassifiedOpcode::allowed("st1"),
    ClassifiedOpcode::allowed("st2"),
    ClassifiedOpcode::allowed("st3"),
    ClassifiedOpcode::allowed("st4"),
    ClassifiedOpcode::allowed("ld1"),
    ClassifiedOpcode::allowed("ld2"),
    ClassifiedOpcode::allowed("ld3"),
    ClassifiedOpcode::allowed("ld4"),
    ClassifiedOpcode::allowed("ld1r"),
    ClassifiedOpcode::allowed("ld2r"),
    ClassifiedOpcode::allowed("ld3r"),
    ClassifiedOpcode::allowed("ld4r"),
    // Allowed: SIMD arithmetic
    ClassifiedOpcode::allowed("shadd"),
    ClassifiedOpcode::allowed("sqadd"),
    ClassifiedOpcode::allowed("srhadd"),
    ClassifiedOpcode::allowed("shsub"),
    ClassifiedOpcode::allowed("sqsub"),
    ClassifiedOpcode::allowed("uhadd"),
    ClassifiedOpcode::allowed("uqadd"),
    ClassifiedOpcode::allowed("urhadd"),
    ClassifiedOpcode::allowed("uhsub"),
    ClassifiedOpcode::allowed("uqsub"),
    ClassifiedOpcode::allowed("addp"),
    ClassifiedOpcode::allowed("addv"),
    ClassifiedOpcode::allowed("addhn"),
    ClassifiedOpcode::allowed("addhn2"),
    ClassifiedOpcode::allowed("raddhn"),
    ClassifiedOpcode::allowed("raddhn2"),
    ClassifiedOpcode::allowed("subhn"),
    ClassifiedOpcode::allowed("subhn2"),
    ClassifiedOpcode::allowed("rsubhn"),
    ClassifiedOpcode::allowed("rsubhn2"),
    // Allowed: SIMD compare
    ClassifiedOpcode::allowed("cmgt"),
    ClassifiedOpcode::allowed("cmge"),
    ClassifiedOpcode::allowed("cmlt"),
    ClassifiedOpcode::allowed("cmle"),
    ClassifiedOpcode::allowed("cmeq"),
    ClassifiedOpcode::allowed("cmhi"),
    ClassifiedOpcode::allowed("cmhs"),
    ClassifiedOpcode::allowed("cmtst"),
    // Allowed: SIMD shifts
    ClassifiedOpcode::allowed("sshr"),
    ClassifiedOpcode::allowed("ssra"),
    ClassifiedOpcode::allowed("srshr"),
    ClassifiedOpcode::allowed("srsra"),
    ClassifiedOpcode::allowed("shl"),
    ClassifiedOpcode::allowed("sqshl"),
    ClassifiedOpcode::allowed("shrn"),
    ClassifiedOpcode::allowed("shrn2"),
    ClassifiedOpcode::allowed("rshrn"),
    ClassifiedOpcode::allowed("rshrn2"),
    ClassifiedOpcode::allowed("sqshrn"),
    ClassifiedOpcode::allowed("sqshrn2"),
    ClassifiedOpcode::allowed("sqrshrn"),
    ClassifiedOpcode::allowed("sqrshrn2"),
    ClassifiedOpcode::allowed("sshll"),
    ClassifiedOpcode::allowed("sshll2"),
    ClassifiedOpcode::allowed("ushr"),
    ClassifiedOpcode::allowed("usra"),
    ClassifiedOpcode::allowed("urshr"),
    ClassifiedOpcode::allowed("ursra"),
    ClassifiedOpcode::allowed("sri"),
    ClassifiedOpcode::allowed("sli"),
    ClassifiedOpcode::allowed("sqshlu"),
    ClassifiedOpcode::allowed("uqshl"),
    ClassifiedOpcode::allowed("sqshrun"),
    ClassifiedOpcode::allowed("sqshrun2"),
    ClassifiedOpcode::allowed("sqrshrun"),
    ClassifiedOpcode::allowed("sqrshrun2"),
    ClassifiedOpcode::allowed("uqshrn"),
    ClassifiedOpcode::allowed("uqshrn2"),
    ClassifiedOpcode::allowed("uqrshrn"),
    ClassifiedOpcode::allowed("uqrshrn2"),
    ClassifiedOpcode::allowed("ushll"),
    ClassifiedOpcode::allowed("ushll2"),
    ClassifiedOpcode::allowed("shll"),
    ClassifiedOpcode::allowed("shll2"),
    ClassifiedOpcode::allowed("sshl"),
    ClassifiedOpcode::allowed("srshl"),
    ClassifiedOpcode::allowed("sqrshl"),
    ClassifiedOpcode::allowed("ushl"),
    ClassifiedOpcode::allowed("urshl"),
    ClassifiedOpcode::allowed("uqrshl"),
    // Allowed: SIMD multiply
    ClassifiedOpcode::allowed("mla"),
    ClassifiedOpcode::allowed("mls"),
    ClassifiedOpcode::allowed("pmul"),
    ClassifiedOpcode::allowed("pmull"),
    ClassifiedOpcode::allowed("pmull2"),
    ClassifiedOpcode::allowed("smull"),
    ClassifiedOpcode::allowed("smull2"),
    ClassifiedOpcode::allowed("umull"),
    ClassifiedOpcode::allowed("umull2"),
    ClassifiedOpcode::allowed("smlal"),
    ClassifiedOpcode::allowed("smlal2"),
    ClassifiedOpcode::allowed("umlal"),
    ClassifiedOpcode::allowed("umlal2"),
    ClassifiedOpcode::allowed("smlsl"),
    ClassifiedOpcode::allowed("smlsl2"),
    ClassifiedOpcode::allowed("umlsl"),
    ClassifiedOpcode::allowed("umlsl2"),
    ClassifiedOpcode::allowed("sqdmulh"),
    ClassifiedOpcode::allowed("sqrdmulh"),
    ClassifiedOpcode::allowed("sqdmull"),
    ClassifiedOpcode::allowed("sqdmull2"),
    ClassifiedOpcode::allowed("sqdmlal"),
    ClassifiedOpcode::allowed("sqdmlal2"),
    ClassifiedOpcode::allowed("sqdmlsl"),
    ClassifiedOpcode::allowed("sqdmlsl2"),
    ClassifiedOpcode::allowed("sqrdmlah"),
    ClassifiedOpcode::allowed("sqrdmlsh"),
    // Allowed: SIMD min/max/abs
    ClassifiedOpcode::allowed("smax"),
    ClassifiedOpcode::allowed("smin"),
    ClassifiedOpcode::allowed("umax"),
    ClassifiedOpcode::allowed("umin"),
    ClassifiedOpcode::allowed("smaxp"),
    ClassifiedOpcode::allowed("sminp"),
    ClassifiedOpcode::allowed("umaxp"),
    ClassifiedOpcode::allowed("uminp"),
    ClassifiedOpcode::allowed("smaxv"),
    ClassifiedOpcode::allowed("sminv"),
    ClassifiedOpcode::allowed("umaxv"),
    ClassifiedOpcode::allowed("uminv"),
    ClassifiedOpcode::allowed("sabd"),
    ClassifiedOpcode::allowed("uabd"),
    ClassifiedOpcode::allowed("saba"),
    ClassifiedOpcode::allowed("uaba"),
    ClassifiedOpcode::allowed("sabdl"),
    ClassifiedOpcode::allowed("sabdl2"),
    ClassifiedOpcode::allowed("uabdl"),
    ClassifiedOpcode::allowed("uabdl2"),
    ClassifiedOpcode::allowed("sabal"),
    ClassifiedOpcode::allowed("sabal2"),
    ClassifiedOpcode::allowed("uabal"),
    ClassifiedOpcode::allowed("uabal2"),
    ClassifiedOpcode::allowed("abs"),
    ClassifiedOpcode::allowed("sqabs"),
    ClassifiedOpcode::allowed("sqneg"),
    // Allowed: SIMD widen/narrow/add
    ClassifiedOpcode::allowed("saddl"),
    ClassifiedOpcode::allowed("saddl2"),
    ClassifiedOpcode::allowed("saddw"),
    ClassifiedOpcode::allowed("saddw2"),
    ClassifiedOpcode::allowed("ssubl"),
    ClassifiedOpcode::allowed("ssubl2"),
    ClassifiedOpcode::allowed("ssubw"),
    ClassifiedOpcode::allowed("ssubw2"),
    ClassifiedOpcode::allowed("uaddl"),
    ClassifiedOpcode::allowed("uaddl2"),
    ClassifiedOpcode::allowed("uaddw"),
    ClassifiedOpcode::allowed("uaddw2"),
    ClassifiedOpcode::allowed("usubl"),
    ClassifiedOpcode::allowed("usubl2"),
    ClassifiedOpcode::allowed("usubw"),
    ClassifiedOpcode::allowed("usubw2"),
    ClassifiedOpcode::allowed("saddlp"),
    ClassifiedOpcode::allowed("sadalp"),
    ClassifiedOpcode::allowed("uaddlp"),
    ClassifiedOpcode::allowed("uadalp"),
    ClassifiedOpcode::allowed("saddlv"),
    ClassifiedOpcode::allowed("uaddlv"),
    // SIMD saturating add
    ClassifiedOpcode::allowed("suqadd"),
    ClassifiedOpcode::allowed("usqadd"),
    // SIMD narrow
    ClassifiedOpcode::allowed("xtn"),
    ClassifiedOpcode::allowed("xtn2"),
    ClassifiedOpcode::allowed("sqxtn"),
    ClassifiedOpcode::allowed("sqxtn2"),
    ClassifiedOpcode::allowed("sqxtun"),
    ClassifiedOpcode::allowed("sqxtun2"),
    ClassifiedOpcode::allowed("uqxtn"),
    ClassifiedOpcode::allowed("uqxtn2"),
    // Allowed: SIMD permute/extract
    ClassifiedOpcode::allowed("ins"),
    ClassifiedOpcode::allowed("ext"),
    ClassifiedOpcode::allowed("dup"),
    ClassifiedOpcode::allowed("uzp1"),
    ClassifiedOpcode::allowed("uzp2"),
    ClassifiedOpcode::allowed("trn1"),
    ClassifiedOpcode::allowed("trn2"),
    ClassifiedOpcode::allowed("zip1"),
    ClassifiedOpcode::allowed("zip2"),
    ClassifiedOpcode::allowed("tbl"),
    ClassifiedOpcode::allowed("tbx"),
    // SIMD move
    ClassifiedOpcode::allowed("smov"),
    ClassifiedOpcode::allowed("umov"),
    ClassifiedOpcode::allowed("movi"),
    ClassifiedOpcode::allowed("mvni"),
    // SIMD bitwise
    ClassifiedOpcode::allowed("bsl"),
    ClassifiedOpcode::allowed("bit"),
    ClassifiedOpcode::allowed("bif"),
    ClassifiedOpcode::allowed("not"),
    ClassifiedOpcode::allowed("cnt"),
    // SIMD dot product (integer)
    ClassifiedOpcode::allowed("sdot"),
    ClassifiedOpcode::allowed("udot"),
    // SIMD reciprocal estimate (integer)
    ClassifiedOpcode::allowed("urecpe"),
    ClassifiedOpcode::allowed("ursqrte"),
    // Allowed: Crypto extensions (deterministic)
    ClassifiedOpcode::allowed("aese"),
    ClassifiedOpcode::allowed("aesd"),
    ClassifiedOpcode::allowed("aesmc"),
    ClassifiedOpcode::allowed("aesimc"),
    ClassifiedOpcode::allowed("sha1c"),
    ClassifiedOpcode::allowed("sha1p"),
    ClassifiedOpcode::allowed("sha1m"),
    ClassifiedOpcode::allowed("sha1h"),
    ClassifiedOpcode::allowed("sha1su0"),
    ClassifiedOpcode::allowed("sha1su1"),
    ClassifiedOpcode::allowed("sha256h"),
    ClassifiedOpcode::allowed("sha256h2"),
    ClassifiedOpcode::allowed("sha256su0"),
    ClassifiedOpcode::allowed("sha256su1"),
    ClassifiedOpcode::allowed("sha512h"),
    ClassifiedOpcode::allowed("sha512h2"),
    ClassifiedOpcode::allowed("sha512su0"),
    ClassifiedOpcode::allowed("sha512su1"),
    ClassifiedOpcode::allowed("sm3ss1"),
    ClassifiedOpcode::allowed("sm3tt1a"),
    ClassifiedOpcode::allowed("sm3tt1b"),
    ClassifiedOpcode::allowed("sm3tt2a"),
    ClassifiedOpcode::allowed("sm3tt2b"),
    ClassifiedOpcode::allowed("sm3partw1"),
    ClassifiedOpcode::allowed("sm3partw2"),
    ClassifiedOpcode::allowed("sm4e"),
    ClassifiedOpcode::allowed("sm4ekey"),
    ClassifiedOpcode::allowed("rax1"),
    ClassifiedOpcode::allowed("xar"),
    ClassifiedOpcode::allowed("bcax"),
    ClassifiedOpcode::allowed("eor3"),
    // Flag manipulation (deterministic)
    ClassifiedOpcode::allowed("setf8"),
    ClassifiedOpcode::allowed("setf16"),
    ClassifiedOpcode::allowed("rmif"),
    // Rejected: Exclusive/atomic loads
    ClassifiedOpcode::rejected("ldxr", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldxrb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldxrh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldxp", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaxr", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaxrb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaxrh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaxp", RejectionReason::Atomic),
    // Exclusive/atomic stores
    ClassifiedOpcode::rejected("stxr", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stxrb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stxrh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stxp", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stlxr", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stlxrb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stlxrh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stlxp", RejectionReason::Atomic),
    // LSE atomic operations
    ClassifiedOpcode::rejected("swp", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swpb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swph", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swpa", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swpab", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swpah", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swpal", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swpalb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swpalh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swpl", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swplb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("swplh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldadd", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldadda", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaddal", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaddl", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaddb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaddab", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaddalb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaddlb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaddh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaddah", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaddalh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaddlh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclr", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclra", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclral", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclrl", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclrb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclrab", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclralb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclrlb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclrh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclrah", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclralh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldclrlh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeor", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeora", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeoral", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeorl", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeorb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeorab", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeoralb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeorlb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeorh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeorah", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeoralh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldeorlh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldset", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldseta", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsetal", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsetl", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsetb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsetab", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsetalb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsetlb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldseth", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsetah", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsetalh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsetlh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmax", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxa", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxal", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxl", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxab", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxalb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxlb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxah", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxalh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmaxlh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmin", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsmina", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsminal", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsminl", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsminb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsminab", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsminalb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsminlb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsminh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsminah", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsminalh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldsminlh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumax", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxa", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxal", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxl", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxab", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxalb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxlb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxah", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxalh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumaxlh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumin", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldumina", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("lduminal", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("lduminl", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("lduminb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("lduminab", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("lduminalb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("lduminlb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("lduminh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("lduminah", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("lduminalh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("lduminlh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("cas", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("casa", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("casal", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("casl", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("casb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("casab", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("casalb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("caslb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("cash", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("casah", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("casalh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("caslh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("casp", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("caspa", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("caspal", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("caspl", RejectionReason::Atomic),
    // Clear exclusive monitor
    ClassifiedOpcode::rejected("clrex", RejectionReason::Atomic),
    // Acquire/release loads/stores
    ClassifiedOpcode::rejected("ldar", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldarb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldarh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldlar", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldlarb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldlarh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldapr", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaprb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldaprh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldapur", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldapurb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldapurh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldapursb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldapursh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("ldapursw", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stlr", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stlrb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stlrh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stllr", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stllrb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stllrh", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stlur", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stlurb", RejectionReason::Atomic),
    ClassifiedOpcode::rejected("stlurh", RejectionReason::Atomic),
    // PAC loads
    ClassifiedOpcode::rejected("ldraa", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("ldrab", RejectionReason::PointerAuth),
    // Rejected: System instructions
    ClassifiedOpcode::rejected("svc", RejectionReason::System),
    ClassifiedOpcode::rejected("hvc", RejectionReason::System),
    ClassifiedOpcode::rejected("smc", RejectionReason::System),
    ClassifiedOpcode::rejected("msr", RejectionReason::System),
    ClassifiedOpcode::rejected("mrs", RejectionReason::System),
    ClassifiedOpcode::rejected("sys", RejectionReason::System),
    ClassifiedOpcode::rejected("sysl", RejectionReason::System),
    ClassifiedOpcode::rejected("dcps1", RejectionReason::System),
    ClassifiedOpcode::rejected("dcps2", RejectionReason::System),
    ClassifiedOpcode::rejected("dcps3", RejectionReason::System),
    ClassifiedOpcode::rejected("drps", RejectionReason::System),
    ClassifiedOpcode::rejected("hlt", RejectionReason::System),
    // ERET variants are also indirect branches
    ClassifiedOpcode::indirect_return("eret"),
    ClassifiedOpcode::indirect_return("eretaa"),
    ClassifiedOpcode::indirect_return("eretab"),
    // Rejected: Memory barriers
    // DMB variants (parameterized by barrier option)
    ClassifiedOpcode::rejected("dmb oshld", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb oshst", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb osh", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb nshld", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb nshst", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb nsh", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb ishld", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb ishst", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb ish", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb ld", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb st", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dmb sy", RejectionReason::Barrier),
    // DSB variants (parameterized by barrier option)
    ClassifiedOpcode::rejected("dsb oshld", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb oshst", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb osh", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb nshld", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb nshst", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb nsh", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb ishld", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb ishst", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb ish", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb ld", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb st", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("dsb sy", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("isb", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("sb", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("ssbb", RejectionReason::Barrier),
    ClassifiedOpcode::rejected("pssbb", RejectionReason::Barrier),
    // Rejected: Indirect branches
    ClassifiedOpcode::indirect_branch("br"),
    ClassifiedOpcode::indirect_call("blr"),
    ClassifiedOpcode::indirect_return("ret"),
    // PAC indirect branches
    ClassifiedOpcode::indirect_branch("braa"),
    ClassifiedOpcode::indirect_branch("braaz"),
    ClassifiedOpcode::indirect_branch("brab"),
    ClassifiedOpcode::indirect_branch("brabz"),
    ClassifiedOpcode::indirect_call("blraa"),
    ClassifiedOpcode::indirect_call("blraaz"),
    ClassifiedOpcode::indirect_call("blrab"),
    ClassifiedOpcode::indirect_call("blrabz"),
    ClassifiedOpcode::indirect_return("retaa"),
    ClassifiedOpcode::indirect_return("retab"),
    ClassifiedOpcode::indirect_return("retaasppc"),
    ClassifiedOpcode::indirect_return("retabsppc"),
    ClassifiedOpcode::indirect_return("retaasppcr"),
    ClassifiedOpcode::indirect_return("retabsppcr"),
    // Rejected: Pointer authentication
    ClassifiedOpcode::rejected("pacia", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacib", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacda", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacdb", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autia", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autib", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autda", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autdb", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("paciza", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacizb", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacdza", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacdzb", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autiza", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autizb", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autdza", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autdzb", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("xpaci", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("xpacd", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacga", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("paciasp", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("paciaz", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacia1716", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacia171615", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("paciasppc", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacnbiasppc", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacibsp", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacibz", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacib1716", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacib171615", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacibsppc", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacnbibsppc", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autiasp", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autiaz", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autia1716", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autia171615", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autiasppc", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autiasppcr", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autibsp", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autibz", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autib1716", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autib171615", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autibsppc", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("autibsppcr", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("xpaclri", RejectionReason::PointerAuth),
    ClassifiedOpcode::rejected("pacm", RejectionReason::PointerAuth),
    // Rejected: Memory tagging extension
    ClassifiedOpcode::rejected("ldgm", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("ldg", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("stgm", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("stzgm", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("stg", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("stzg", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("st2g", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("stz2g", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("gmi", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("irg", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("subp", RejectionReason::MemoryTagging),
    ClassifiedOpcode::rejected("subps", RejectionReason::MemoryTagging),
    // Rejected: Floating-point instructions
    ClassifiedOpcode::rejected("fmadd", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmsub", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fnmadd", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fnmsub", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("scvtf", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("ucvtf", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtzs", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtzu", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtns", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtps", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtms", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtas", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtnu", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtmu", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtau", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtpu", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtn", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtn2", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtl", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtl2", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtxn", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvtxn2", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("bfcvt", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcvt", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fjcvtzs", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmov", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fabs", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fneg", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fsqrt", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frintn", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frintp", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frintm", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frintz", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frinta", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frintx", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frinti", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frint32z", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frint32x", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frint64z", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frint64x", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcmp", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcmpe", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fccmp", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fccmpe", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcmeq", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcmge", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcmgt", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcmle", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcmlt", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmul", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fdiv", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fadd", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fsub", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmax", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmin", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmaxnm", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fminnm", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fnmul", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmulx", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fabd", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcsel", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmla", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmls", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmlal", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmlal2", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmlsl", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmlsl2", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcmla", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fcadd", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmaxnmv", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fminnmv", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmaxv", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fminv", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("faddp", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmaxnmp", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fminnmp", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fmaxp", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("fminp", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("facge", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("facgt", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frecpe", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frecpx", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frecps", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frsqrte", RejectionReason::FloatingPoint),
    ClassifiedOpcode::rejected("frsqrts", RejectionReason::FloatingPoint),
];

lazy_static! {
    /// Map from mnemonic string to ClassifiedOpcode
    pub static ref BY_MNEMONIC: HashMap<&'static str, &'static ClassifiedOpcode> = {
        OPCODE_TABLE.iter().map(|c| (c.mnemonic, c)).collect()
    };
}

#[cfg(test)]
mod tests {
    use yaxpeax_arm::armv8::a64::Opcode;

    use crate::{CheckResult, ClassifiedOpcode, RejectionReason};

    #[test]
    fn test_classify_add() {
        let c = ClassifiedOpcode::from_opcode(Opcode::ADD);
        assert_eq!(c.mnemonic, "add");
        assert_eq!(c.check_result, CheckResult::Allowed);
        assert!(!c.is_branch);
    }

    #[test]
    fn test_classify_branch() {
        let c = ClassifiedOpcode::from_opcode(Opcode::B);
        assert_eq!(c.mnemonic, "b");
        assert!(c.is_branch);
        assert!(!c.is_call);
        assert!(!c.is_indirect);
        assert_eq!(c.check_result, CheckResult::Allowed);
    }

    #[test]
    fn test_classify_bl() {
        let c = ClassifiedOpcode::from_opcode(Opcode::BL);
        assert_eq!(c.mnemonic, "bl");
        assert!(c.is_branch);
        assert!(c.is_call);
        assert!(!c.is_indirect);
        assert_eq!(c.check_result, CheckResult::Allowed);
    }

    #[test]
    fn test_classify_conditional_branch() {
        let c = ClassifiedOpcode::from_opcode(Opcode::Bcc(0)); // 0 = EQ condition
        assert_eq!(c.mnemonic, "b.eq");
        assert!(c.is_branch);
        assert!(c.is_conditional);
        assert!(!c.is_indirect);
        assert_eq!(c.check_result, CheckResult::Allowed);
    }

    #[test]
    fn test_classify_ret() {
        let c = ClassifiedOpcode::from_opcode(Opcode::RET);
        assert_eq!(c.mnemonic, "ret");
        assert!(c.is_branch);
        assert!(c.is_return);
        assert!(c.is_indirect);
        assert_eq!(
            c.check_result,
            CheckResult::Rejected(RejectionReason::IndirectBranch)
        );
    }

    #[test]
    fn test_classify_blr() {
        let c = ClassifiedOpcode::from_opcode(Opcode::BLR);
        assert_eq!(c.mnemonic, "blr");
        assert!(c.is_branch);
        assert!(c.is_call);
        assert!(c.is_indirect);
        assert_eq!(
            c.check_result,
            CheckResult::Rejected(RejectionReason::IndirectBranch)
        );
    }

    #[test]
    fn test_classify_unknown() {
        let c = &ClassifiedOpcode::UNKNOWN;
        assert_eq!(c.mnemonic, "unknown");
        assert_eq!(
            c.check_result,
            CheckResult::Rejected(RejectionReason::Unknown)
        );
    }

    #[test]
    fn test_from_mnemonic() {
        let c = ClassifiedOpcode::from_mnemonic("add").unwrap();
        assert_eq!(c.mnemonic, "add");
        assert_eq!(c.check_result, CheckResult::Allowed);

        let c = ClassifiedOpcode::from_mnemonic("b.eq").unwrap();
        assert_eq!(c.mnemonic, "b.eq");
        assert!(c.is_branch);
        assert!(c.is_conditional);

        assert!(ClassifiedOpcode::from_mnemonic("nonexistent").is_none());
    }

    #[test]
    fn test_eret_is_indirect_return() {
        let c = ClassifiedOpcode::from_opcode(Opcode::ERET);
        assert_eq!(c.mnemonic, "eret");
        assert!(c.is_branch);
        assert!(c.is_return);
        assert!(c.is_indirect);
        assert_eq!(
            c.check_result,
            CheckResult::Rejected(RejectionReason::IndirectBranch)
        );
    }

    #[test]
    fn test_unknown_mnemonic_returns_none() {
        assert!(ClassifiedOpcode::from_mnemonic("notarealinstruction").is_none());
        assert!(ClassifiedOpcode::from_mnemonic("xyz").is_none());
    }
}
