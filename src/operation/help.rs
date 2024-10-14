//! Help messages, for use in diagnostics
use std::borrow::Cow;

pub(super) const NO_OPCODE: Cow<'static, str> = Cow::Borrowed(
    "All instructions must begin with a cluster, and then an opcode (e.g., `add`, `ldw`, ...)",
);
pub(super) const BAD_CLUSTER: Cow<'static, str> =
    Cow::Borrowed("Clusters must begin with the letter `c`");
pub(super) const NO_CLUSTER: Cow<'static, str> =
    Cow::Borrowed("All instructions must begin with a cluster");
pub(super) const BAD_PAYLOAD: Cow<'static, str> = Cow::Borrowed(
    "This instruction requires a payload in matching parentheses, like (_?STRINGPACKET.1...)",
);
pub(super) const CLUSTER_MISMATCH: Cow<'static, str> = Cow::Borrowed("This instruction only supports registers in a single cluster. Have you considered using SEND & RECV?");
pub(super) const NO_REG_CLUSTER: Cow<'static, str> =
    Cow::Borrowed("All registers must have a cluster");
