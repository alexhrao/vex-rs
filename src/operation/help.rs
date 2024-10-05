pub(super) const NO_OPCODE: &str =
    "All instructions must begin with a cluster, and then an opcode (e.g., `add`, `ldw`, ...)";
pub(super) const BAD_CLUSTER: &str = "Clusters must begin with the letter `c`";
pub(super) const NO_CLUSTER: &str = "All instructions must begin with a cluster";
pub(super) const BAD_PAYLOAD: &str =
    "This instruction requires a payload in matching parentheses, like (_?STRINGPACKET.1...)";
