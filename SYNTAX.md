# Vela 0.7 language specification

Status: experimental scalar, fixed-array, named-record and owned numeric-buffer subset, 2026-11-09. This specification describes the Rust compiler. Unsupported designs belong in proposals, not in executable grammar. No stable ABI or compatibility promise extends beyond this version.

## Lexical rules

Sources are UTF-8 `.vela` files. CRLF and LF line endings are accepted. Identifiers match `[A-Za-z_][A-Za-z_0-9]*` and are case-sensitive. Reserved names are `craft keep change when otherwise repeat give say true false and or not num flag text use as len record buffer buffer_copy`.

A nonblank statement occupies one physical line. Blocks indent exactly one level of four spaces relative to their parent. Tabs cannot supply indentation; horizontal tabs between tokens are whitespace. Blank lines and comment-only lines do not change block structure. `#` starts a comment outside a string. There are no statement semicolons, multiline expressions, or brace-delimited blocks. Braces delimit named record values; semicolons separate array element/count syntax.

Integer tokens contain decimal digits without separators, suffixes or leading sign. Values must fit a signed 64-bit integer after applying an immediately preceding unary minus. `-9223372036854775808` is valid; positive `9223372036854775808` is invalid. Negating a computed minimum integer traps at runtime.

Double-quoted text supports raw UTF-8 and JSON-style escapes: `\"`, `\\`, `\/`, `\n`, `\r`, `\t`, `\b`, `\f`, and `\uXXXX` (including valid surrogate pairs). Unescaped control characters, invalid escapes, unmatched quotes/surrogates, and embedded NUL are errors. Strings cannot span physical lines.

## Grammar

The EBNF below omits whitespace/comment tokens. `NEWLINE`, `INDENT`, and `DEDENT` describe the line/block structure enforced by the parser. Each suite must contain at least one statement. `IDENT`, `INTEGER`, and `TEXT` follow the lexical rules above. Import paths are text tokens.

```ebnf
file       = { import | function | record } ;
import     = "use", TEXT, "as", IDENT, NEWLINE ;
record     = "record", IDENT, ":", NEWLINE, INDENT, field, { field }, DEDENT ;
field      = IDENT, ":", type, NEWLINE ;
function   = "craft", IDENT, "(", [ params ], ")", "->", type, ":", suite ;
params     = param, { ",", param } ;
param      = IDENT, ":", type ;
type       = scalar | "buffer" | "[", scalar, ";", LENGTH, "]" | named ;
named      = IDENT, [ ".", IDENT ] ;
scalar     = "num" | "flag" | "text" ;
suite      = NEWLINE, INDENT, statement, { statement }, DEDENT ;
statement  = ("keep" | "change"), IDENT, "=", expr, NEWLINE
           | place, "=", expr, NEWLINE
           | "say", expr, NEWLINE
           | "give", expr, NEWLINE
           | "when", expr, ":", suite, [ "otherwise", ":", suite ]
           | "repeat", expr, ":", suite ;
expr       = or_expr ;
place      = IDENT, { ".", IDENT | "[", expr, "]" } ;
or_expr    = and_expr, { "or", and_expr } ;
and_expr   = comparison, { "and", comparison } ;
comparison = sum, { ("==" | "!=" | "<" | "<=" | ">" | ">="), sum } ;
sum        = product, { ("+" | "-"), product } ;
product    = prefix, { ("*" | "/" | "%"), prefix } ;
prefix     = ("-" | "not"), prefix | postfix ;
postfix    = atom, { "[", expr, "]" | ".", IDENT } ;
atom       = INTEGER | TEXT | "true" | "false" | "(", expr, ")"
           | IDENT | callee, "(", [ args ], ")"
           | named, "{", [ initializers ], "}"
           | "[", [ expr, { ",", expr } ], "]"
           | "[", expr, ";", LENGTH, "]"
           | "len", "(", expr, ")"
           | "buffer", "(", expr, ")"
           | "buffer_copy", "(", expr, ")" ;
callee     = IDENT, [ ".", IDENT ] ;
args       = expr, { ",", expr } ;
initializers = IDENT, ":", expr, { ",", IDENT, ":", expr } ;
```

Calls bind more tightly than prefix operators. Binary operators associate left. Chained comparisons are **not** Python-style mathematical chains: `1 < 2 < 3` parses as `(1 < 2) < 3` and fails type checking. `not` binds more tightly than comparisons for compatibility with the prototype; write `not (a == b)` when negating a comparison. Trailing commas are not supported. Only named functions can be called; functions are not values. Expression-only call statements are not supported.

## Types, names and scopes

| Type | Current value representation | Supported operations |
| --- | --- | --- |
| `num` | Signed 64 integer | Arithmetic and ordered/equality comparison |
| `flag` | Canonical false/true scalar | `and`, `or`, `not`, equality/inequality |
| `text` | Immutable NUL-terminated UTF-8 static data with process lifetime | Pass, copy, return and `say`; no comparison, indexing, mutation or concatenation |
| `buffer` | Affine owner of a runtime-length, zero-initialized numeric sequence | Whole-value moves, explicit deep copy, named-local length and checked numeric indexing |
| `[SCALAR; LENGTH]` | Contiguous fixed-length value, eight bytes per scalar element | Copy, pass, return, checked element access, `len`; no aggregate printing/equality |
| Named record | Contiguous fields in declaration order; nested value layouts | Named construction, independent copies, fields, typed projected writes; no aggregate printing/equality |

No implicit conversions exist. Conditions require `flag`; arithmetic requires `num`. Function parameter/return types are explicit. Local types are inferred from initializers and remain fixed. Variables require initialization and cannot refer to themselves in that initializer unless an outer binding of the same name is visible.

Array lengths are literal decimal integers 1..4096; element type and length form exact type identity. Lists infer a homogeneous scalar type; empty, mixed and nested array literals are rejected by semantic checking. Repeated literals `[value; LENGTH]` evaluate the scalar initializer exactly once. Array copies on declaration, assignment, parameter passing and return are independent; a copy cannot mutate its source. `keep` arrays and array parameters reject element writes. `change` permits same-type whole replacement and element mutation.

Indexing evaluates its array expression and then its `num` index. Bounds require `0 <= index < LENGTH` and are checked in every mode, including constant indices; failures print `vela runtime error: array index out of bounds` to stdout and exit 71. Indexed assignment supports a named local followed by field/index projections: evaluate each index, check its bounds, then evaluate the RHS and write. A failing index prevents RHS side effects. `len(array_expression)` returns `num` and preserves operand evaluation/faults; direct local/field length and index reads are O(1). Creating/copying an array costs O(length); by-value calls may currently copy more than once. There are no slices, source pointers, nested arrays, arrays of records, implicit array conversions, array equality or array printing. Runtime-length numeric storage is the separate owned `buffer` type below.

Array values have no source-visible address. The internal ABI uses snapshots, callee-local parameter copies and caller-provided result storage. Returning an array copies it before the callee frame ends. Six source parameters are still allowed; a hidden array-result pointer is additional machine state, not a source parameter. The ABI remains experimental.

`keep` and parameters are immutable bindings. `change` permits reassignment, but does not imply a new type, allocation, or mutable string contents. Function bodies share their parameter scope; nested branches and loop bodies introduce separate scopes. Same-scope redeclarations are errors; inner scopes may shadow outer bindings. Branch-local variables never escape their branch. Each loop iteration executes its declarations again. There are no globals, closures or first-class functions.

Function signatures are collected before bodies, allowing recursion, mutual recursion, and forward calls. Duplicate functions or parameter names are errors. Functions and record declarations share a module declaration namespace. A function supports at most six arguments, and every call must match its signature. Function calls and local variable values occupy distinct syntactic/name roles: a local variable is never callable. Module aliases also have a separate namespace from variables; alias/declaration collisions are rejected.

## Named records and assignment places

`record Point:` introduces a nonempty indented list of explicitly typed fields. A field can contain a scalar, a fixed scalar array or another named record, including a forward declaration. Record types are nominal: different declarations remain incompatible even when all fields match. Direct/indirect by-value cycles have no finite layout and are rejected with a trace. Function recursion is independent of type-layout recursion.

`Point { y: 9, x: 7 }` initializes every declared field exactly once. Unknown, missing, repeated or incorrectly typed fields are errors. Initializers evaluate in written source order; declaration order determines storage. There are no defaults, methods, callable fields, inheritance, type aliases or destructuring. Field names must be non-keyword identifiers. Empty record types are unsupported.

Read fields with `point.x`, `sample.point.x` or `make().point.x`. Records and all contained fields have value-copy semantics on declaration, assignment, arguments and return. `keep` and parameters prohibit projected mutation; `change` permits same-type writes. A place starts at a named local and appends field/index projections, such as `sample.point.x` or `sample.values[i]`; arbitrary expression bases are not assignable. Indices/checks precede RHS evaluation. Writing an aggregate field copies its entire selected value independently.

Scalar fields occupy eight bytes, and arrays/nested records contribute their complete word widths. Fields are contiguous with no extra padding, in declaration order. Direct local field paths resolve to constant offsets and do not copy containing records. A field value that is passed or assigned by value may require an aggregate copy. Aggregate construction/copy/argument/return costs O(total words), sometimes with multiple copies; there is no hidden heap allocation or mandatory GC for these values.

Record results use caller-owned result storage and the same experimental hidden-pointer ABI as arrays. No returned record or field may depend on a dead callee frame. Records are not source pointers, heap owners or borrowed references; their implemented behavior is not a general lifetime-checker guarantee. Layout and frame limits apply, and runtime recursion can still exhaust the stack.

## Owned numeric buffers

`buffer(length)` evaluates a `num` length once, allocates a sequence and zero-initializes every cell. Zero length is valid. Valid lengths are 0..1152921504606846974, preventing signed byte-size overflow with the private length header. Invalid length or null allocation prints `vela runtime error: invalid buffer length or allocation failure` to stdout and exits 72. Large valid lengths can fail allocation; success is not guaranteed.

`len(owner)`, `owner[index]` and `buffer_copy(owner)` inspect a direct named buffer local without moving it. Bind a returned/allocated temporary first; general borrowed expressions are unsupported. Indexing checks `0 <= index < len(owner)` and faults with status 71 and the same bounds message as fixed arrays. `buffer_copy` allocates independent numeric contents. Only a `change` binding permits element writes or whole replacement. An indexed-store index and check precede its RHS; neither the index nor RHS may consume that owner.

Buffers transfer on declaration, whole assignment, arguments and return; they never copy implicitly. `keep` and parameters prevent mutation, but allow transfer. Using a moved value is an error with related declaration/move source notes. A `change` binding can be reinitialized; `owner = owner` transfers out and back without releasing its allocation. Arguments evaluate left to right and consuming one owner twice is rejected. A branch join permits use only when every continuing path preserves availability. Loop conditions cannot consume existing owners, and each falling loop-body backedge must restore outer owners moved in the body. Zero iterations cannot initialize a moved owner. Short-circuit RHS moves count as possibly executed even for constant conditions, because checking precedes optimization.

Scope fallthrough releases live owners in reverse declaration order. Return evaluates/captures its result, then releases remaining local/parameter owners in reverse declaration order; returning an owner transfers it to the caller. Replacement evaluates the RHS, releases the old destination if still owned, then installs the incoming value. Moved-from/inactive bindings have a private null state and no allocation to release. Buffers cannot occur inside records or arrays; no partial moves, exposed references, raw pointers, resizing, slices or user destructors exist.

Normal exits have exactly-once ownership cleanup in the implemented subset. Arithmetic, bounds and allocation faults (70/71/72) terminate the process without unwinding or cleanup guarantees. External termination, operating-system memory exhaustion and stack exhaustion are not recovered. There is no mandatory tracing collector or reference-counting runtime. Allocation/deallocation use target libc; no general soundness or hard latency bound is claimed.

## Evaluation and arithmetic

Evaluation is left-to-right, including function arguments. `and`/`or` short circuit; their operands are still statically checked. Vela has no truthiness conversions. Signed comparisons do not use arithmetic subtraction, so extreme operands compare without overflow.

Integer addition, subtraction, multiplication and unary negation are checked in all compilation modes. Overflow, division/remainder by zero, and either `MIN / -1` or `MIN % -1` terminate the process with status 70. The current runtime prints `vela runtime error: integer overflow or invalid division` to stdout, then calls the C runtime's `exit`. Runtime faults lack source locations and do not unwind or run user cleanup; user destructors do not exist.

Division truncates toward zero. Remainder has the dividend's sign. There are no wrapping, saturating or unchecked arithmetic operators yet. Constant folding preserves the same fault behavior: invalid arithmetic is left for runtime checking, and an unevaluated short-circuit operand cannot cause a fault.

`say` prints one value followed by a newline. `flag` prints `true` or `false`, and `num` prints signed decimal. Text is passed to `puts`, never used as a formatting directive. Windows CRT newline conversion can produce CRLF; UTF-8 bytes are emitted, while console rendering depends on the terminal. I/O error recovery is not specified yet.

## Control flow and entry point

`give` returns a value matching the function's declared result. Every function must return on every conservatively recognized path. An `if` returns only if both branches return. A loop is never assumed to execute or terminate, even if its condition is literal `true`; add a following `give`. Statements following a recognized unconditional return are errors. There are no implicit zero returns, `break`, `continue`, exceptions or implicit tail returns.

The entry file must define `craft main() -> num:` without parameters. Its return contributes the low eight bits to process exit status in both built executables and `run`. Imported functions named `main` are ordinary module functions and do not replace the entry point. Arithmetic faults use status 70 independently of the returned value.

## Local modules

Imports occur at column one, outside functions:

```vela
use "math.vela" as math

craft main() -> num:
    say math.square(12)
    give 0
```

Paths use `/`, are relative to the importing file, and must have a `.vela` suffix. Absolute paths, Windows drive prefixes and backslash separators are rejected. Canonical paths, including resolved symlinks, must stay inside the entry file's directory tree. `..` is permitted only when canonical containment still holds. There is no module search path, implicit standard-library lookup, network resolution or package registry.

Each canonical file is loaded once in a graph; import cycles are errors with a trace. Duplicate aliases and alias/declaration collisions are errors. Functions and record types defined in a module are accessible through the alias; there are no visibility modifiers or re-exports. A module may contain only record declarations. Unqualified calls/types see only the current file's declarations. Qualified calls, types and record constructors accept one alias and one declaration name, for example `geometry.Point` and `geometry.Point { x: 1, y: 2 }`. Record value field paths may be longer; methods and `a.b.c()` calls are unsupported. Dependencies need no `main`. Imports have no runtime initialization side effects.

Both parse and semantic diagnostics, including related ownership notes, refer to the original module path, physical line, and Unicode-scalar column. Imported names are internally qualified; `ir` currently exposes those names and graph-wide line coordinates as an unstable debugging representation.

## Diagnostics and limits

The lexer collects independent line errors, the parser recovers at the next top-level function or record, and semantic checking collects independent name/type/control-flow errors. The first failing stage stops compilation; diagnostics from later stages are not fabricated from an invalid AST. Import loading may stop on the first dependency error.

Limits are 128 nested block/parser levels, 256 expression-construction steps per line, 64 active import levels, 128 modules, 8 MiB total source bytes and 4096 elements per fixed array. Machine functions allow 65536 blocks and 262144 typed temporary ids. Actual allocated fixed frames are capped at 65536 eight-byte words, including locals, live temporary slots and an aggregate result pointer. Noninterfering temporary lifetimes can share ranges; named locals remain distinct. A conservative structured-IR expression-size estimate can exceed the native frame cap without rejection if the machine allocation fits. Fixed locals and actual native frames are checked independently. Expression construction counts atoms, groups, prefixes, calls, indexing and binary operators; repeat literals do not expand the parser node budget. These implementation limits are diagnosed but are not language expressiveness goals or a general resource-exhaustion proof. Runtime recursion has no safe depth limit.

Records add limits of 1024 declared types per graph, 128 fields per record, 64 nested record levels and 16384 eight-byte words per record layout. Field labels do not themselves consume expression-construction steps; their initializer values, constructors and postfix projections do. Checked canonical layouts reject mismatched cached widths/offsets and cycles before code generation. The current IR dump includes internal record ids and unstable graph-wide coordinates.

`check` verifies the machine graph and storage capacity as well as source semantics; `ir` retains the structured debugging view and `cfg` shows typed machine blocks. Both native modes use liveness and a small call-aware scalar register allocator. Release graph dead-definition removal preserves checked arithmetic, bounds, writes, output and unknown calls. The graph is not full SSA: short-circuit result ids may be assigned on multiple incoming edges. Compiler graph/assembly changes do not alter the evaluation/fault semantics above.

## Compatibility with Vela 0.2

Version 0.7 adds whole-value owned numeric buffers and reserves `buffer` and `buffer_copy`; earlier declarations with those names must be renamed. `copy` remains an ordinary user name. Version 0.6 changed the native compiler pipeline, added `cfg` inspection and admitted more sequential-temporary sources after lifetime-based storage reuse. Version 0.5 added named records and reserved `record`; version 0.4 added value arrays and reserved `len`. Internal IR/ABIs remain experimental with no binary compatibility promise. Earlier scalar semantics below remain applicable.

The three supplied examples retain their behavior. The Rust compiler adds Win64 output and modules, source spans, integer bounds/faults and complete-return checks. Falling off a function now fails compilation. Text containing NUL now fails instead of truncating on output. Type names and `use`/`as` are reserved. Integer overflow now traps instead of wrapping. These are intentional pre-stability changes. The Python reference remains unchanged.
