//! Instruction whitelist for deterministic execution
//!
//! Based on the DeCl paper (OSDI 2025), this module defines which Arm64 instructions
//! are allowed in deterministic code.
//!
//! # Approach
//!
//! We use an explicit whitelist where every known opcode is categorized. The
//! `Opcode` enum is marked `#[non_exhaustive]` by yaxpeax-arm, so we need a catch-all
//! `_` arm. This achieves our security goal: any new/unknown opcode added in future
//! versions is rejected by default until we explicitly review and categorize it.
//!
//! # Rejected categories
//!
//! - **Atomic/Exclusive**: LDXR, STXR, SWP, CAS, etc. - depend on exclusive monitor state
//! - **System**: SVC, MSR, MRS, etc. - interact with privileged state
//! - **Barriers**: DMB, DSB, ISB - affect memory ordering
//! - **Floating point**: FADD, FMUL, etc. - implementation-defined precision
//! - **Indirect branches**: BR, BLR, RET - require rewriting to verified pattern

use yaxpeax_arm::armv8::a64::Opcode;

use crate::DecodedInstruction;

/// Result of checking an instruction against the whitelist
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckResult {
    /// Instruction is allowed
    Allowed,
    /// Instruction is rejected with a reason
    Rejected(RejectionReason),
}

/// Reason an instruction was rejected
#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// Unknown/invalid instruction
    Invalid,
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
            RejectionReason::Invalid => write!(f, "invalid/unknown instruction"),
        }
    }
}

/// Check if an instruction is allowed in deterministic code
///
/// All known opcodes are explicitly categorized. The catch-all `_` arm
/// rejects any unknown/future opcodes as `Invalid` - this is the secure default.
#[allow(deprecated)] // for SSSB
pub fn check(instr: &DecodedInstruction) -> CheckResult {
    use CheckResult::*;
    use RejectionReason::*;

    match instr.opcode() {
        Opcode::Invalid => Rejected(Invalid),

        // Allowed: base integer arithmetic
        Opcode::ADD
        | Opcode::ADDS
        | Opcode::SUB
        | Opcode::SUBS
        | Opcode::ADC
        | Opcode::ADCS
        | Opcode::SBC
        | Opcode::SBCS
        | Opcode::NEG => Allowed,

        // Multiply/divide
        Opcode::MADD
        | Opcode::MSUB
        | Opcode::SMADDL
        | Opcode::SMSUBL
        | Opcode::SMULH
        | Opcode::UMADDL
        | Opcode::UMSUBL
        | Opcode::UMULH
        | Opcode::UDIV
        | Opcode::SDIV
        | Opcode::MUL => Allowed,

        // Allowed: logic operations
        Opcode::AND
        | Opcode::ANDS
        | Opcode::ORR
        | Opcode::ORN
        | Opcode::EOR
        | Opcode::EON
        | Opcode::BIC
        | Opcode::BICS
        | Opcode::NOT => Allowed,

        // Allowed: move instructions
        Opcode::MOVN | Opcode::MOVK | Opcode::MOVZ => Allowed,

        // Allowed: bit manipulation
        Opcode::BFM
        | Opcode::UBFM
        | Opcode::SBFM
        | Opcode::EXTR
        | Opcode::RBIT
        | Opcode::REV
        | Opcode::REV16
        | Opcode::REV32
        | Opcode::REV64
        | Opcode::CLZ
        | Opcode::CLS => Allowed,

        // Allowed: shifts
        Opcode::LSLV | Opcode::LSRV | Opcode::ASRV | Opcode::RORV => Allowed,

        // Allowed: address generation
        Opcode::ADR | Opcode::ADRP => Allowed,

        // Allowed: non-exclusive loads
        Opcode::LDP
        | Opcode::LDPSW
        | Opcode::LDR
        | Opcode::LDRB
        | Opcode::LDRSB
        | Opcode::LDRSW
        | Opcode::LDRSH
        | Opcode::LDRH
        | Opcode::LDTR
        | Opcode::LDTRB
        | Opcode::LDTRH
        | Opcode::LDTRSB
        | Opcode::LDTRSH
        | Opcode::LDTRSW
        | Opcode::LDUR
        | Opcode::LDURB
        | Opcode::LDURSB
        | Opcode::LDURSW
        | Opcode::LDURSH
        | Opcode::LDURH
        | Opcode::LDNP => Allowed,

        // Allowed: non-exclusive stores
        Opcode::STP
        | Opcode::STR
        | Opcode::STRB
        | Opcode::STRH
        | Opcode::STRW
        | Opcode::STTR
        | Opcode::STTRB
        | Opcode::STTRH
        | Opcode::STUR
        | Opcode::STURB
        | Opcode::STURH
        | Opcode::STNP => Allowed,

        // Allowed: direct branches (targets verifiable)
        Opcode::B | Opcode::BL | Opcode::Bcc(_) | Opcode::BCcc(_) => Allowed,

        // Allowed: compare and branch
        Opcode::TBZ | Opcode::TBNZ | Opcode::CBZ | Opcode::CBNZ => Allowed,

        // Allowed: conditional select/compare
        Opcode::CSEL
        | Opcode::CSNEG
        | Opcode::CSINC
        | Opcode::CSINV
        | Opcode::CCMN
        | Opcode::CCMP => Allowed,

        // Allowed: CRC (deterministic)
        Opcode::CRC32B
        | Opcode::CRC32H
        | Opcode::CRC32W
        | Opcode::CRC32X
        | Opcode::CRC32CB
        | Opcode::CRC32CH
        | Opcode::CRC32CW
        | Opcode::CRC32CX => Allowed,

        // Allowed: hints (NOP, etc.) and special
        Opcode::HINT => Allowed,

        // BRK is allowed for gas trap (brk #0)
        Opcode::BRK => Allowed,

        // UDF is allowed for explicit undefined instruction trap
        Opcode::UDF => Allowed,

        // Prefetch (no side effects on program state)
        Opcode::PRFM | Opcode::PRFUM => Allowed,

        // Allowed: SIMD vector loads/stores
        Opcode::ST1
        | Opcode::ST2
        | Opcode::ST3
        | Opcode::ST4
        | Opcode::LD1
        | Opcode::LD2
        | Opcode::LD3
        | Opcode::LD4
        | Opcode::LD1R
        | Opcode::LD2R
        | Opcode::LD3R
        | Opcode::LD4R => Allowed,

        // SIMD arithmetic
        Opcode::SHADD
        | Opcode::SQADD
        | Opcode::SRHADD
        | Opcode::SHSUB
        | Opcode::SQSUB
        | Opcode::UHADD
        | Opcode::UQADD
        | Opcode::URHADD
        | Opcode::UHSUB
        | Opcode::UQSUB
        | Opcode::ADDP
        | Opcode::ADDV
        | Opcode::ADDHN
        | Opcode::ADDHN2
        | Opcode::RADDHN
        | Opcode::RADDHN2
        | Opcode::SUBHN
        | Opcode::SUBHN2
        | Opcode::RSUBHN
        | Opcode::RSUBHN2 => Allowed,

        // SIMD compare
        Opcode::CMGT
        | Opcode::CMGE
        | Opcode::CMLT
        | Opcode::CMLE
        | Opcode::CMEQ
        | Opcode::CMHI
        | Opcode::CMHS
        | Opcode::CMTST => Allowed,

        // SIMD shifts
        Opcode::SSHR
        | Opcode::SSRA
        | Opcode::SRSHR
        | Opcode::SRSRA
        | Opcode::SHL
        | Opcode::SQSHL
        | Opcode::SHRN
        | Opcode::SHRN2
        | Opcode::RSHRN
        | Opcode::RSHRN2
        | Opcode::SQSHRN
        | Opcode::SQSHRN2
        | Opcode::SQRSHRN
        | Opcode::SQRSHRN2
        | Opcode::SSHLL
        | Opcode::SSHLL2
        | Opcode::USHR
        | Opcode::USRA
        | Opcode::URSHR
        | Opcode::URSRA
        | Opcode::SRI
        | Opcode::SLI
        | Opcode::SQSHLU
        | Opcode::UQSHL
        | Opcode::SQSHRUN
        | Opcode::SQSHRUN2
        | Opcode::SQRSHRUN
        | Opcode::SQRSHRUN2
        | Opcode::UQSHRN
        | Opcode::UQSHRN2
        | Opcode::UQRSHRN
        | Opcode::UQRSHRN2
        | Opcode::USHLL
        | Opcode::USHLL2
        | Opcode::SHLL
        | Opcode::SHLL2
        | Opcode::SSHL
        | Opcode::SRSHL
        | Opcode::SQRSHL
        | Opcode::USHL
        | Opcode::URSHL
        | Opcode::UQRSHL => Allowed,

        // SIMD multiply
        Opcode::MLA
        | Opcode::MLS
        | Opcode::PMUL
        | Opcode::PMULL
        | Opcode::PMULL2
        | Opcode::SMULL
        | Opcode::SMULL2
        | Opcode::UMULL
        | Opcode::UMULL2
        | Opcode::SMLAL
        | Opcode::SMLAL2
        | Opcode::UMLAL
        | Opcode::UMLAL2
        | Opcode::SMLSL
        | Opcode::SMLSL2
        | Opcode::UMLSL
        | Opcode::UMLSL2
        | Opcode::SQDMULH
        | Opcode::SQRDMULH
        | Opcode::SQDMULL
        | Opcode::SQDMULL2
        | Opcode::SQDMLAL
        | Opcode::SQDMLAL2
        | Opcode::SQDMLSL
        | Opcode::SQDMLSL2
        | Opcode::SQRDMLAH
        | Opcode::SQRDMLSH => Allowed,

        // SIMD min/max/abs
        Opcode::SMAX
        | Opcode::SMIN
        | Opcode::UMAX
        | Opcode::UMIN
        | Opcode::SMAXP
        | Opcode::SMINP
        | Opcode::UMAXP
        | Opcode::UMINP
        | Opcode::SMAXV
        | Opcode::SMINV
        | Opcode::UMAXV
        | Opcode::UMINV
        | Opcode::SABD
        | Opcode::UABD
        | Opcode::SABA
        | Opcode::UABA
        | Opcode::SABDL
        | Opcode::SABDL2
        | Opcode::UABDL
        | Opcode::UABDL2
        | Opcode::SABAL
        | Opcode::SABAL2
        | Opcode::UABAL
        | Opcode::UABAL2
        | Opcode::ABS
        | Opcode::SQABS
        | Opcode::SQNEG => Allowed,

        // SIMD widen/narrow/add
        Opcode::SADDL
        | Opcode::SADDL2
        | Opcode::SADDW
        | Opcode::SADDW2
        | Opcode::SSUBL
        | Opcode::SSUBL2
        | Opcode::SSUBW
        | Opcode::SSUBW2
        | Opcode::UADDL
        | Opcode::UADDL2
        | Opcode::UADDW
        | Opcode::UADDW2
        | Opcode::USUBL
        | Opcode::USUBL2
        | Opcode::USUBW
        | Opcode::USUBW2
        | Opcode::SADDLP
        | Opcode::SADALP
        | Opcode::UADDLP
        | Opcode::UADALP
        | Opcode::SADDLV
        | Opcode::UADDLV => Allowed,

        // SIMD saturating add
        Opcode::SUQADD | Opcode::USQADD => Allowed,

        // SIMD narrow
        Opcode::XTN
        | Opcode::XTN2
        | Opcode::SQXTN
        | Opcode::SQXTN2
        | Opcode::SQXTUN
        | Opcode::SQXTUN2
        | Opcode::UQXTN
        | Opcode::UQXTN2 => Allowed,

        // SIMD permute/extract
        Opcode::INS
        | Opcode::EXT
        | Opcode::DUP
        | Opcode::UZP1
        | Opcode::UZP2
        | Opcode::TRN1
        | Opcode::TRN2
        | Opcode::ZIP1
        | Opcode::ZIP2
        | Opcode::TBL
        | Opcode::TBX => Allowed,

        // SIMD move
        Opcode::SMOV | Opcode::UMOV | Opcode::MOVI | Opcode::MVNI => Allowed,

        // SIMD bitwise
        Opcode::BSL | Opcode::BIT | Opcode::BIF | Opcode::CNT => Allowed,

        // SIMD dot product (integer)
        Opcode::SDOT | Opcode::UDOT => Allowed,

        // SIMD reciprocal estimate (integer)
        Opcode::URECPE | Opcode::URSQRTE => Allowed,

        // Allowed: crypto extensions (deterministic)
        Opcode::AESE
        | Opcode::AESD
        | Opcode::AESMC
        | Opcode::AESIMC
        | Opcode::SHA1C
        | Opcode::SHA1P
        | Opcode::SHA1M
        | Opcode::SHA1H
        | Opcode::SHA1SU0
        | Opcode::SHA1SU1
        | Opcode::SHA256H
        | Opcode::SHA256H2
        | Opcode::SHA256SU0
        | Opcode::SHA256SU1
        | Opcode::SHA512H
        | Opcode::SHA512H2
        | Opcode::SHA512SU0
        | Opcode::SHA512SU1
        | Opcode::SM3SS1
        | Opcode::SM3TT1A
        | Opcode::SM3TT1B
        | Opcode::SM3TT2A
        | Opcode::SM3TT2B
        | Opcode::SM3PARTW1
        | Opcode::SM3PARTW2
        | Opcode::SM4E
        | Opcode::SM4EKEY
        | Opcode::RAX1
        | Opcode::XAR
        | Opcode::BCAX
        | Opcode::EOR3 => Allowed,

        // Allowed: flag manipulation (deterministic)
        Opcode::SETF8 | Opcode::SETF16 | Opcode::RMIF => Allowed,

        // Rejected: exclusive/atomic loads (depend on monitor state)
        Opcode::LDXR
        | Opcode::LDXRB
        | Opcode::LDXRH
        | Opcode::LDXP
        | Opcode::LDAXR
        | Opcode::LDAXRB
        | Opcode::LDAXRH
        | Opcode::LDAXP => Rejected(Atomic),

        // Rejected: exclusive/atomic stores
        Opcode::STXR
        | Opcode::STXRB
        | Opcode::STXRH
        | Opcode::STXP
        | Opcode::STLXR
        | Opcode::STLXRB
        | Opcode::STLXRH
        | Opcode::STLXP => Rejected(Atomic),

        // Rejected: atomic operations (LSE extension)
        Opcode::SWP(_)
        | Opcode::SWPB(_)
        | Opcode::SWPH(_)
        | Opcode::LDADDB(_)
        | Opcode::LDADDH(_)
        | Opcode::LDADD(_)
        | Opcode::LDCLRB(_)
        | Opcode::LDCLRH(_)
        | Opcode::LDCLR(_)
        | Opcode::LDEORB(_)
        | Opcode::LDEORH(_)
        | Opcode::LDEOR(_)
        | Opcode::LDSETB(_)
        | Opcode::LDSETH(_)
        | Opcode::LDSET(_)
        | Opcode::LDSMAXB(_)
        | Opcode::LDSMAXH(_)
        | Opcode::LDSMAX(_)
        | Opcode::LDSMINB(_)
        | Opcode::LDSMINH(_)
        | Opcode::LDSMIN(_)
        | Opcode::LDUMAXB(_)
        | Opcode::LDUMAXH(_)
        | Opcode::LDUMAX(_)
        | Opcode::LDUMINB(_)
        | Opcode::LDUMINH(_)
        | Opcode::LDUMIN(_)
        | Opcode::CAS(_)
        | Opcode::CASB(_)
        | Opcode::CASH(_)
        | Opcode::CASP(_) => Rejected(Atomic),

        // Clear exclusive monitor
        Opcode::CLREX => Rejected(Atomic),

        // Rejected: acquire/release loads/stores (memory ordering)
        Opcode::LDAR
        | Opcode::LDARB
        | Opcode::LDARH
        | Opcode::LDLAR
        | Opcode::LDLARB
        | Opcode::LDLARH
        | Opcode::LDAPR
        | Opcode::LDAPRB
        | Opcode::LDAPRH
        | Opcode::LDAPUR
        | Opcode::LDAPURB
        | Opcode::LDAPURH
        | Opcode::LDAPURSB
        | Opcode::LDAPURSH
        | Opcode::LDAPURSW
        | Opcode::STLR
        | Opcode::STLRB
        | Opcode::STLRH
        | Opcode::STLLR
        | Opcode::STLLRB
        | Opcode::STLLRH
        | Opcode::STLUR
        | Opcode::STLURB
        | Opcode::STLURH => Rejected(Atomic),

        // PAC loads (pointer authentication)
        Opcode::LDRAA | Opcode::LDRAB => Rejected(PointerAuth),

        // Rejected: system instructions
        Opcode::SVC | Opcode::HVC | Opcode::SMC => Rejected(System),
        Opcode::MSR | Opcode::MRS => Rejected(System),
        Opcode::SYS(_) | Opcode::SYSL(_) => Rejected(System),
        Opcode::DCPS1 | Opcode::DCPS2 | Opcode::DCPS3 | Opcode::DRPS => Rejected(System),
        Opcode::HLT => Rejected(System),
        Opcode::ERET | Opcode::ERETAA | Opcode::ERETAB => Rejected(System),

        // Rejected: memory barriers
        Opcode::DMB(_) | Opcode::DSB(_) | Opcode::ISB | Opcode::SB => Rejected(Barrier),
        Opcode::SSBB | Opcode::PSSBB | Opcode::SSSB => Rejected(Barrier),

        // Rejected: indirect branches (require rewriting)
        Opcode::BR | Opcode::BLR | Opcode::RET => Rejected(IndirectBranch),

        // PAC indirect branches
        Opcode::BRAA
        | Opcode::BRAAZ
        | Opcode::BRAB
        | Opcode::BRABZ
        | Opcode::BLRAA
        | Opcode::BLRAAZ
        | Opcode::BLRAB
        | Opcode::BLRABZ
        | Opcode::RETAA
        | Opcode::RETAB
        | Opcode::RETAASPPC
        | Opcode::RETABSPPC
        | Opcode::RETAASPPCR
        | Opcode::RETABSPPCR => Rejected(IndirectBranch),

        // Rejected: pointer authentication (depends on system keys)
        Opcode::PACIA
        | Opcode::PACIB
        | Opcode::PACDA
        | Opcode::PACDB
        | Opcode::AUTIA
        | Opcode::AUTIB
        | Opcode::AUTDA
        | Opcode::AUTDB
        | Opcode::PACIZA
        | Opcode::PACIZB
        | Opcode::PACDZA
        | Opcode::PACDZB
        | Opcode::AUTIZA
        | Opcode::AUTIZB
        | Opcode::AUTDZA
        | Opcode::AUTDZB
        | Opcode::XPACI
        | Opcode::XPACD
        | Opcode::PACGA
        | Opcode::PACIASP
        | Opcode::PACIAZ
        | Opcode::PACIA1716
        | Opcode::PACIA171615
        | Opcode::PACIASPPC
        | Opcode::PACNBIASPPC
        | Opcode::PACIBSP
        | Opcode::PACIBZ
        | Opcode::PACIB1716
        | Opcode::PACIB171615
        | Opcode::PACIBSPPC
        | Opcode::PACNBIBSPPC
        | Opcode::AUTIASP
        | Opcode::AUTIAZ
        | Opcode::AUTIA1716
        | Opcode::AUTIA171615
        | Opcode::AUTIASPPC
        | Opcode::AUTIASPPCR
        | Opcode::AUTIBSP
        | Opcode::AUTIBZ
        | Opcode::AUTIB1716
        | Opcode::AUTIB171615
        | Opcode::AUTIBSPPC
        | Opcode::AUTIBSPPCR
        | Opcode::XPACLRI
        | Opcode::PACM => Rejected(PointerAuth),

        // Rejected: memory tagging extension
        Opcode::LDGM
        | Opcode::LDG
        | Opcode::STGM
        | Opcode::STZGM
        | Opcode::STG
        | Opcode::STZG
        | Opcode::ST2G
        | Opcode::STZ2G
        | Opcode::GMI
        | Opcode::IRG
        | Opcode::SUBP
        | Opcode::SUBPS => Rejected(MemoryTagging),

        // Rejected: floating-point instructions
        Opcode::FMADD | Opcode::FMSUB | Opcode::FNMADD | Opcode::FNMSUB => Rejected(FloatingPoint),

        // Conversions
        Opcode::SCVTF
        | Opcode::UCVTF
        | Opcode::FCVTZS
        | Opcode::FCVTZU
        | Opcode::FCVTNS
        | Opcode::FCVTPS
        | Opcode::FCVTMS
        | Opcode::FCVTAS
        | Opcode::FCVTNU
        | Opcode::FCVTMU
        | Opcode::FCVTAU
        | Opcode::FCVTPU
        | Opcode::FCVTN
        | Opcode::FCVTN2
        | Opcode::FCVTL
        | Opcode::FCVTL2
        | Opcode::FCVTXN
        | Opcode::FCVTXN2
        | Opcode::BFCVT
        | Opcode::FCVT
        | Opcode::FJCVTZS => Rejected(FloatingPoint),

        // Basic ops
        Opcode::FMOV | Opcode::FABS | Opcode::FNEG | Opcode::FSQRT => Rejected(FloatingPoint),

        // Rounding
        Opcode::FRINTN
        | Opcode::FRINTP
        | Opcode::FRINTM
        | Opcode::FRINTZ
        | Opcode::FRINTA
        | Opcode::FRINTX
        | Opcode::FRINTI
        | Opcode::FRINT32Z
        | Opcode::FRINT32X
        | Opcode::FRINT64Z
        | Opcode::FRINT64X => Rejected(FloatingPoint),

        // Compare
        Opcode::FCMP
        | Opcode::FCMPE
        | Opcode::FCCMP
        | Opcode::FCCMPE
        | Opcode::FCMEQ
        | Opcode::FCMGE
        | Opcode::FCMGT
        | Opcode::FCMLE
        | Opcode::FCMLT => Rejected(FloatingPoint),

        // Arithmetic
        Opcode::FMUL
        | Opcode::FDIV
        | Opcode::FADD
        | Opcode::FSUB
        | Opcode::FMAX
        | Opcode::FMIN
        | Opcode::FMAXNM
        | Opcode::FMINNM
        | Opcode::FNMUL
        | Opcode::FMULX
        | Opcode::FABD => Rejected(FloatingPoint),

        // Conditional
        Opcode::FCSEL => Rejected(FloatingPoint),

        // Vector ops
        Opcode::FMLA
        | Opcode::FMLS
        | Opcode::FMLAL
        | Opcode::FMLAL2
        | Opcode::FMLSL
        | Opcode::FMLSL2
        | Opcode::FCMLA
        | Opcode::FCADD => Rejected(FloatingPoint),

        // Reductions
        Opcode::FMAXNMV
        | Opcode::FMINNMV
        | Opcode::FMAXV
        | Opcode::FMINV
        | Opcode::FADDP
        | Opcode::FMAXNMP
        | Opcode::FMINNMP
        | Opcode::FMINMNP
        | Opcode::FMAXP
        | Opcode::FMINP => Rejected(FloatingPoint),

        // Absolute comparisons
        Opcode::FACGE | Opcode::FACGT => Rejected(FloatingPoint),

        // Reciprocal
        Opcode::FRECPE | Opcode::FRECPX | Opcode::FRECPS | Opcode::FRSQRTE | Opcode::FRSQRTS => {
            Rejected(FloatingPoint)
        }

        // Catch-all: reject unknown/future opcodes (secure default)
        _ => Rejected(Invalid),
    }
}

#[cfg(test)]
mod tests {
    use super::{check, CheckResult, RejectionReason};
    use crate::decode_instructions;

    #[test]
    fn test_allowed_add() {
        // add x0, x1, x2 -> 0x8b020020
        let code = [0x20, 0x00, 0x02, 0x8b];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(check(&instrs[0]), CheckResult::Allowed);
    }

    #[test]
    fn test_allowed_mov() {
        // mov x0, #1 -> 0xd2800020
        let code = [0x20, 0x00, 0x80, 0xd2];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(check(&instrs[0]), CheckResult::Allowed);
    }

    #[test]
    fn test_allowed_branch() {
        // b #8 -> 0x14000002
        let code = [0x02, 0x00, 0x00, 0x14];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(check(&instrs[0]), CheckResult::Allowed);
    }

    #[test]
    fn test_allowed_load() {
        // ldr x0, [x1] -> 0xf9400020
        let code = [0x20, 0x00, 0x40, 0xf9];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(check(&instrs[0]), CheckResult::Allowed);
    }

    #[test]
    fn test_allowed_store() {
        // str x0, [x1] -> 0xf9000020
        let code = [0x20, 0x00, 0x00, 0xf9];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(check(&instrs[0]), CheckResult::Allowed);
    }

    #[test]
    fn test_allowed_brk() {
        // brk #0 -> 0xd4200000 (allowed for gas trap)
        let code = [0x00, 0x00, 0x20, 0xd4];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(check(&instrs[0]), CheckResult::Allowed);
    }

    #[test]
    fn test_rejected_atomic_ldxr() {
        // ldxr x0, [x1] -> 0xc85f7c20
        let code = [0x20, 0x7c, 0x5f, 0xc8];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::Atomic)
        );
    }

    #[test]
    fn test_rejected_atomic_stxr() {
        // stxr w2, x0, [x1] -> 0xc8027c20
        let code = [0x20, 0x7c, 0x02, 0xc8];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::Atomic)
        );
    }

    #[test]
    fn test_rejected_system_svc() {
        // svc #0 -> 0xd4000001
        let code = [0x01, 0x00, 0x00, 0xd4];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::System)
        );
    }

    #[test]
    fn test_rejected_system_mrs() {
        // mrs x0, nzcv -> 0xd53b4200
        let code = [0x00, 0x42, 0x3b, 0xd5];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::System)
        );
    }

    #[test]
    fn test_rejected_barrier_dmb() {
        // dmb sy -> 0xd5033fbf
        let code = [0xbf, 0x3f, 0x03, 0xd5];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::Barrier)
        );
    }

    #[test]
    fn test_rejected_fp_fadd() {
        // fadd d0, d1, d2 -> 0x1e622820
        let code = [0x20, 0x28, 0x62, 0x1e];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::FloatingPoint)
        );
    }

    #[test]
    fn test_rejected_indirect_br() {
        // br x0 -> 0xd61f0000
        let code = [0x00, 0x00, 0x1f, 0xd6];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::IndirectBranch)
        );
    }

    #[test]
    fn test_rejected_indirect_ret() {
        // ret -> 0xd65f03c0
        let code = [0xc0, 0x03, 0x5f, 0xd6];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::IndirectBranch)
        );
    }

    #[test]
    fn test_rejected_indirect_blr() {
        // blr x8 -> 0xd63f0100
        let code = [0x00, 0x01, 0x3f, 0xd6];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::IndirectBranch)
        );
    }

    #[test]
    fn test_rejected_pointer_auth_paciasp() {
        // paciasp -> 0xd503233f
        let code = [0x3f, 0x23, 0x03, 0xd5];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::PointerAuth)
        );
    }

    #[test]
    fn test_rejected_memory_tagging_irg() {
        // irg x0, x1 -> 0x9ac11c20
        let code = [0x20, 0x10, 0xdf, 0x9a];
        let instrs = decode_instructions(&code).unwrap();
        assert_eq!(
            check(&instrs[0]),
            CheckResult::Rejected(RejectionReason::MemoryTagging)
        );
    }
}
