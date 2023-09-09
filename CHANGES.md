## v1.1

### Added

- Parsing and disambiguation of non-normal expressions is supported.
- Parsing of prefix, infix and postfix operators is supported for computation-level type family constants and constructors, as well as type-annotated programs and values.
- Improved error-reporting with printing of source code.
- Pretty-printing of Beluga signatures to HTML now supports hyperlinks for constants to their declaration site.

### Changed

- Substitution meta-objects need to be prefixed by `$`. That is, the plain substitution `[g |- $S]` must be written as `$[g |- $S]`, and the renaming substitution `[g |-# $S]` must be written as `$[g |-# $S]`.
- Substitution meta-types need to be prefixed by `$`. That is, the plain substitution meta-type `[g |- h]` must be written as `$[g |- h]`, and the renaming substitution meta-type `[g |-# h]` must be written as `$[g |-# h]`.
- Parameter types need to be prefixed by `#`. That is, `{#p : [g |- nat]}` must be written as `{#p : #[g |- nat]}`.
- Identifier overloading is disallowed. This means that term-level constants may not be overloaded with type-level constants.
- Freezing of type family declarations is more strict. This means that old-style LF term-level constants cannot be added to type families after any declaration other than old-style LF type or term-level constant declarations.
- Destructors for coinductive type families use postfix notation, like projections or field accesses (i.e., `s .hd`, `s .tl`). This applies both in computation-level patterns and expressions.
- Namespaces are now fully supported in Beluga signatures.

### Fixed

- Interactive Harpoon sessions are now local to the referencing environment in which they are declared.
- Lexing of nested delimited comments `%{{`, `}}%` and `%{`, `}%` is fixed.
- `--open` pragmas behave like OCaml's `open` directive, whereby declarations introduced by `--open` are not re-exported, and not copy/pasted textually.

### Removed

- Harpoon sequencing of REPL commands with `;` is no longer supported.
- Context variable arrow types `[ctx] → [⊢ unit]` are no longer supported.