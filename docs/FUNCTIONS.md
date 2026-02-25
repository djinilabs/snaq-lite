# Functions

This document describes how to define and call functions (both user-defined and built-in) and what the built-in functions do.

## User-defined functions

You can define functions with optional default parameters and call them by name. Names in the body refer to parameters and to variables from the surrounding scope (closures).

### Defining functions

- **Anonymous:** `fn ( param1, param2, ... ) => ( expression )` or `fn ( param1, ... ) => { block }`. For a single parameter you can omit the parentheses: `fn param => ( expression )` or `fn param => { block }`.
  - Example: `fn (a, b) => (a + b)` — a function that adds two arguments.
  - Example: `fn n => (n * 10)` — single-argument shorthand; same as `fn (n) => (n * 10)`.
- **Named:** `fn name ( param1, param2, ... ) => ( expression )` or `fn name ( param1, ... ) => { block }`. For a single parameter you can omit the parentheses: `fn name param => ( expression )` or `fn name param => { block }`.
  - Example: `fn mysum(a, b) => (a + b)` — defines `mysum` in the current block; later expressions can call `mysum(1, 2)`.
  - Example: `fn double n => (n * 2)` — single-argument shorthand; same as `fn double (n) => (n * 2)`.

Parameters can have **default values:** `param = expression`. Defaults are evaluated in the function’s closure scope when the argument is omitted at call time.

- Example: `fn add(a, b = 10) => (a + b)` — `add(5)` gives 15, `add(5, 3)` gives 8.

The body can be a single expression in parentheses or a **block** `{ ... }` (semicolon- or newline-separated expressions; the result is the last expression). The parentheses or braces are required so the parser knows where the body ends (e.g. use `fn n => (n * 10)`, not `fn n => n * 10`).

- Example: `fn f(a, b) => { x = a + b; x + 42 }` — block body with a local binding.

### Calling user-defined functions

- **By name:** After a named definition, use the same call syntax as built-ins: `name ( arg1, arg2, ... )`.
- **Arguments:** Positional and named arguments work the same as for built-ins. Positional arguments are bound in order; named arguments (e.g. `b: 2`) can appear in any order and override or supply parameters by name.

If a name is bound to a user-defined function in the current scope, that function is used. **Built-in names (sin, cos, tan, max, min) cannot be shadowed:** you cannot bind a variable or function to those names (see [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md)).

### Closures

The body of a function can use variables from the scope where the function was defined. Those values are captured when the function is created.

- Example: `x = 100; fn addx(n) => (n + x); addx(5)` → 105.

### Errors and edge cases (user-defined)

- **Required parameters:** Every parameter that has no default must receive an argument (positional or named). Otherwise you get an error such as "missing argument for parameter 'name'".
- **Unknown parameter name:** Using a named argument whose name is not a parameter (e.g. `f(z: 1)` when `f` has no parameter `z`) is an error.
- **Duplicate parameter:** Passing the same parameter name more than once in a call (e.g. `f(a: 1, a: 2)`) is an error.
- **Too many arguments:** Passing more positional arguments than the number of parameters is an error.
- **Not callable:** If you apply arguments to a value that is not a function (e.g. a number), the runtime reports that the expression is not callable.

When the result of a program (or block) is a function value—for example, when the last expression is a function definition—it displays as `<function>` and cannot be converted to a numeric quantity.

### Vector `.map`

The vector method `V.map(fn (x) => body)` (or the shorthand `V.map(fn x => (body))`) requires its argument to be a **function of exactly one parameter**. Passing a function with zero or two-or-more parameters (e.g. `[1, 2].map(fn (a, b) => (a+b))`) yields an error. See [VECTORS.md](VECTORS.md) for vector properties and methods.

## Call syntax

- **Form:** `name ( arg1, arg2, ... )` — the identifier must be immediately followed by `(` so the parser treats it as a function call (see [SYNTAX.md](SYNTAX.md)).
- **Arguments:** Each argument can be:
  - **Positional:** an expression (e.g. `sin(pi rad)`, `max(3, 2)`).
  - **Named:** `name : expression` (e.g. `max(a: 1, b: 2)`).

Positional and named arguments can be mixed. The language binds positional arguments first, then named arguments (which can override or fill in parameters by name).

## Built-in functions

### Trigonometric: sin, cos, tan

- **Arity:** One argument.
- **Argument:** Must have **angle** dimension (e.g. in radians or degrees). The value is converted to radians internally for computation.
- **Result:** Dimensionless number (or symbolic expression for exact well-known angles). Variance is propagated when the argument has uncertainty.

**Well-known angles:** At certain angles (e.g. 0, π/6, π/4, π/3, π/2, π in radians, or 0°, 30°, 45°, 60°, 90°, 180° in degrees), the result may be returned in **exact symbolic form** (e.g. √2/2, √3/2) when the result is kept symbolic. When you request a numeric result, these are substituted to numbers.

**Errors:**

- **Unknown function** — if the name is not a built-in.
- **Expected angle** — if the argument is not an angle (e.g. `sin(1 m)` or `sin(1)` without a unit). For a dimensionless argument, the error message may suggest adding the `rad` unit (e.g. `sin(pi * rad)`).
- **Wrong arity** — e.g. `sin(1, 2)`.

### max, min

- **Arity:** Two arguments.
- **Arguments:** Must have the **same dimension** (e.g. two lengths, two times, two dimensionless numbers). Unit conversion is applied if needed.
- **Result:** The maximum or minimum of the two values, in the same dimension. If one or both arguments are symbolic, the result may be symbolic.

**Errors:**

- **Unknown function** — if the name is not a built-in.
- **Dimension mismatch** — if the two arguments have different dimensions (e.g. `max(1 m, 2 s)`).
- **Wrong arity** — e.g. `max(1)`.

### sqrt

- **Arity:** One argument.
- **Argument:** Non-negative value (dimensionless or any dimension; e.g. area for length result).
- **Result:** Square root; result unit is the argument unit raised to 1/2 (e.g. sqrt(4 m²) → 2 m). Variance is propagated. When applied to a **vector**, **element-wise** (same as sin/cos/tan).

**Errors:**

- **Invalid argument** — if the argument is negative (e.g. `sqrt(-1)`). The message indicates that the argument must be non-negative.

## Use cases and edge cases

- **Trig with units:** Prefer angle units so the argument is clearly an angle: `sin(pi rad)`, `sin(180 degree)`. Avoid `sin(pi)` without a unit when you mean radians; the runtime may report expected angle (dimensionless).
- **Named arguments:** Useful for clarity, e.g. `max(a: 3, b: 2)` or mixing: `max(3, b: 2)`.
- **Vector arguments:** Unary functions (sin, cos, tan, sqrt) accept a **vector** and apply **element-wise**; the result is a vector. For max/min with one vector and one scalar, or two vectors, behaviour is as defined by the language (element-wise or reduction as for other binary operations; see [VECTORS.md](VECTORS.md) if applicable).

## See also

- [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md) — bindings and that built-in function names cannot be shadowed
- [SYNTAX.md](SYNTAX.md) — identifiers and function call tokenization
- [UNITS_AND_QUANTITIES.md](UNITS_AND_QUANTITIES.md) — angle units (rad, degree)
- [VECTORS.md](VECTORS.md) — functions applied to vectors
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — unknown function, expected angle, dimension mismatch
- [README.md](README.md) — language overview and index
