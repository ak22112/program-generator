# Thoughts

<!-- markdownlint-disable MD013 MD024-->

Keeping track of what I've done and what I'm thinking each day I work on this
project.

## Week 3

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

  - create a `Program` data type that track the number of statements in the program
    - this way you can verify length of program
    - prevents infinite programs
    - also can give the generator function a length as an argument

- overall, struggling to work out where I need to do proofs
  - it feels like the data types defining the grammar are already doing a lot
    of the work
  - this makes me think I need to come up with some properties that I want to
    explicitly prove

## Week 4

- Hardcoding grammar meant that any generator would be correct by definition

  - this means no need for dependent types

- Instead, generator needs to be of the form:

  ```agda
  generator : (g : Grammar) (s : List Symbol) → String g s
  ```

  - takes in a grammer and a list of symbols
  - returns a string over the grammar and symbols
  - String is an indexed data type, dependent on both the grammar and the symbols

- `String` needs to be defined like this:

  ```agda
  data String : (g : Grammar) → (s : List Symbol) → Set where
  ```

  - String is indexed by grammar

### Questions

- Should I say Symbols are the builtin `String` type or should I use a finite data type

## 23/02/2025

### Questions

- Nice way of explaining the benefits of dependent types
- Who is the report written for? What level should it be aimed at?
- Automatic proof finder (using decidability)
