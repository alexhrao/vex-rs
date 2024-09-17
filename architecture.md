# Mode of Operation

After parsing, we have a series of `Group`s. We then start the simulation loop. This loop does the following:

1. Read instructions from the current group. For each instruction, the "effect" is decided; for example, an ALU operation will calculate the result. The return value is a struct that describes how to **commit** the result (e.g., store a value in memory, or write to a register). This is loaded into an available unit.
2. Units are queried, and their results are committed, if necessary
3. The cycle count is incremented