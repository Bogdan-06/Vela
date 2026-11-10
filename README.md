<div align="center">

# Vela

**Readable code. Native binaries.**

A programming language built from the ground up in Rust.

[Get started](#get-started) · [Language reference](SYNTAX.md) · [Examples](examples)

</div>

---

Vela pairs a small, indentation-based syntax with a native x86-64 compiler. Write functions with `craft`, bind values with `keep` or `change`, and return them with `give`.

```vela
craft sum(values: buffer) -> num:
    change result = 0
    change i = 0
    repeat i < len(values):
        result = result + values[i]
        i = i + 1
    give result

craft main() -> num:
    change values = buffer(3)
    values[0] = 10
    values[1] = 20
    values[2] = 30
    say sum(values)
    give 0
```

### Small syntax, real compiler

| Feature | What it means |
| :--- | :--- |
| Native output | Compiles to x86-64 assembly and links an executable. No translation into C or Rust. |
| Static types | Signed 64-bit integers, booleans, static text, fixed arrays, named records, and owned numeric buffers. |
| Explicit ownership | Buffers move between bindings and functions. Deep copies are explicit; live owners are released at normal scope exits. |
| Checked operations | Integer overflow, invalid division, and out-of-bounds indexing produce runtime faults. |
| Local modules | Import `.vela` files with explicit aliases. |
| Inspectable pipeline | View typed IR, control-flow graphs, or emitted assembly from the CLI. |

### Get started

You need Rust and an x86-64 GCC toolchain. Vela currently targets **Windows GNU x64** and **Linux x86-64**. On Windows, use Rust's GNU toolchain with MinGW-w64 on `PATH`.

```sh
git clone https://github.com/Bogdan-06/Vela.git
cd Vela
cargo build --release
```

Run an example:

```sh
# Linux
./target/release/vela run examples/hello.vela

# Windows PowerShell
.\target\release\vela.exe run examples\hello.vela
```

### CLI

```sh
vela check program.vela
vela run program.vela
vela build program.vela --release -o program
vela ir program.vela
vela cfg program.vela
vela asm program.vela
```

Use the built executable's path in place of `vela`, or add it to your `PATH`. On Windows, use an `.exe` output name. `--release` enables constant folding and conservative dead-code removal; arithmetic and bounds checks remain enabled.

### Explore

- [Hello world](examples/hello.vela)
- [Loops and functions](examples/loops.vela)
- [Fixed arrays](examples/arrays.vela)
- [Named records](examples/records.vela)
- [Owned buffers](examples/buffers.vela)
- [Local modules](examples/modules/main.vela)

### Project status

**Experimental · 0.7.0.** Vela is under active development. Syntax and internal interfaces may change. Borrowed references, owned record fields, a package manager, and a full standard library are still ahead.

Buffers have whole-value ownership and normal-exit cleanup. Runtime faults terminate the process without unwinding. General memory-safety guarantees and performance parity with mature native compilers have not been established.
