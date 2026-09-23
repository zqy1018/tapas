# Advice For AI Agents

## General Advice

- The docstring of definitions should be user-facing (i.e., not containing technical details) and brief. The technical details can be put into `/- ... -/` comment blocks near the docstring.
- **DO NOT** remove comments that start with `NOTE:`, `TODO`, `CHECK`, `FIXME:` when editing the code.
- Avoid defining helper definitions or theorems that are only used once, unless you envision they will be used again later.
- Avoid re-inventing the wheel, *especially when writing meta-programs*. That is to say, when you are trying to implement certain functionality (either a meta-program, a normal program or a proof) which seems very general, you should first try to find it in the Lean source code or in the dependencies of the current project. 
- **DO NOT** stage or commit when you finish writing something, unless explicitly and clearly instructed. 

## Lean Tricks

- To leave an instance-implicit argument for unification to fill, write `(_)` rather than `_`. 

## Writing Test Cases

- Unless for the test cases that depend on each other, all test cases should only have a single import for `Tapas`.
- Test cases should be readable and focusing on the things to test. It is discouraged to write a bunch of meta programs in test cases. 
- Use utilities from `TapasTest/TestingUtils.lean` properly. 

## Writing Documentations (Including Comment Blocks)

- **DO NOT** use any terminology that is unspecified. In other words, use a terminology unless it's well-defined (either something well known by the public, or you've defined it clearly before introducing it). 
