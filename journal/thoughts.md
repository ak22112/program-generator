# Thoughts

Keeping track of what I've done and what I'm thinking each day I work on this
project.

## 03/02/2025

### Done

- Defined basic grammar of WHILE language [here](https://github.com/ak22112/program-generator/blob/cd4496eafd5430505d9ddcfb48cc368ef8de3a3a/grammar/Grammar.agda).

### Questions

- Should I use infix operators to define the grammer of the language?

  - | Pros          | Cons                                 |
    | ------------- | ------------------------------------ |
    | More readable | Probably harder for pattern matching |
    |               | Harder to convert AST -> String      |

  - Maybe only for some, e.g. `Seq`, `Assign`

- Where can I start introducing dependent types?
