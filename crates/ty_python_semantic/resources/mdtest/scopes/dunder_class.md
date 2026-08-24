# The `__class__` closure cell

Python implicitly creates a closure cell named `__class__` for methods defined in a class body. The
cell is available in instance methods, static methods, and class methods.

## Method scopes

```py
class C:
    def method(self) -> None:
        reveal_type(__class__)  # revealed: <class 'C'>

    @staticmethod
    def static_method() -> None:
        reveal_type(__class__)  # revealed: <class 'C'>

    @classmethod
    def class_method(cls) -> None:
        reveal_type(__class__)  # revealed: <class 'C'>
```

## Lambda scopes

Lambdas defined directly in a class body also capture the cell. Lambda parameters continue to take
precedence over it.

```py
class C:
    lambda_method = lambda: reveal_type(__class__)  # revealed: <class 'C'>
    shadowed = lambda __class__: reveal_type(__class__)  # revealed: Unknown
```

## Generator expression scopes

The body of a generator expression defined directly in a class captures the cell because it is
evaluated lazily. The first iterable is evaluated eagerly in the class body, where the cell is not
yet available. Eager comprehension bodies likewise cannot access the cell.

```py
class C:
    values = (
        reveal_type(__class__)  # revealed: <class 'C'>
        for _ in range(1)
    )

    first_iterable = (
        value
        for value in (
            __class__,  # error: [unresolved-reference]
        )
    )

    eager_comprehension = [
        __class__  # error: [unresolved-reference]
        for _ in range(1)
    ]
```

## Class bodies and method defaults

The cell is not available directly in the class body or while evaluating a method's default
arguments.

```py
class C:
    __class__  # error: [unresolved-reference]

    def method(
        self,
        value=__class__,  # error: [unresolved-reference]
    ) -> None: ...
```

## Shadowing

The implicit cell takes precedence over a global with the same name. Local bindings and explicit
`global` declarations continue to take precedence over the cell.

```py
__class__ = int

class D:
    def implicit(self) -> None:
        reveal_type(__class__)  # revealed: <class 'D'>

    def local(self) -> None:
        __class__ = str
        reveal_type(__class__)  # revealed: <class 'str'>

    def explicit_global(self) -> None:
        global __class__
        reveal_type(__class__)  # revealed: <class 'int'>
```

## Nested function scopes

Nested functions and lambdas inherit the enclosing method's implicit cell, just as they inherit an
explicit closure binding. Comprehensions and eagerly evaluated nested definitions can also load it
after the method has started executing.

```py
class C:
    def method(self) -> None:
        def nested() -> None:
            reveal_type(__class__)  # revealed: <class 'C'>

            def deeper() -> None:
                reveal_type(__class__)  # revealed: <class 'C'>

        callback = lambda: reveal_type(__class__)  # revealed: <class 'C'>
        values = [reveal_type(__class__) for _ in range(1)]  # revealed: <class 'C'>

        def with_default(value=__class__) -> None:
            reveal_type(value)  # revealed: Unknown | <class 'C'>

        class Inner:
            enclosing = reveal_type(__class__)  # revealed: <class 'C'>

    nested_lambda = lambda: lambda: reveal_type(__class__)  # revealed: <class 'C'>
    nested_generator = (lambda: reveal_type(__class__) for _ in range(1))  # revealed: <class 'C'>
```

## Nested shadowing

Only an actual enclosing implicit-cell boundary supplies the class. Nearer explicit bindings and
scope declarations still control name resolution.

```py
__class__ = int

class C:
    def local(self) -> None:
        __class__ = str

        def nested() -> None:
            reveal_type(__class__)  # revealed: <class 'str'>

    def parameter(self, __class__: int) -> None:
        def nested() -> None:
            reveal_type(__class__)  # revealed: int

    def declared(self) -> None:
        __class__: int

        def nested() -> None:
            # A declared type is not evidence that the runtime cell is bound.
            reveal_type(__class__)  # revealed: int

    def forwarded_nonlocal(self) -> None:
        __class__ = str

        def middle() -> None:
            nonlocal __class__

            def nested() -> None:
                reveal_type(__class__)  # revealed: <class 'str'>

    def forwarded_global(self) -> None:
        global __class__

        def nested() -> None:
            reveal_type(__class__)  # revealed: <class 'int'>

    def nested_global(self) -> None:
        def nested() -> None:
            global __class__
            reveal_type(__class__)  # revealed: <class 'int'>

    def nested_local(self) -> None:
        def nested() -> None:
            __class__ = bytes
            reveal_type(__class__)  # revealed: <class 'bytes'>

    def unbound_nested(self) -> None:
        def nested() -> None:
            __class__  # error: [unresolved-reference]
            __class__ = str
```

## No implicit owner

Class namespace membership is not lexical closure provenance. A function assigned to a class does
not gain a class cell, and an enclosing class body does not supply one to a nested class body.

```py
def outside() -> None:
    def nested() -> None:
        __class__  # error: [unresolved-reference]

class C:
    method = outside

    class Inner:
        __class__  # error: [unresolved-reference]

    def forwarded_global(self) -> None:
        global __class__  # error: [unresolved-global]

        def nested() -> None:
            __class__  # error: [unresolved-reference]
```

## Known limitations

The following uses need additional binding or annotation-scope producer support.

### Explicit nonlocal declarations of the implicit cell

The lookup can now reach the implicit cell, but declaration validation still requires an explicit
enclosing binding. Both declarations below are valid in Python and remain a known limitation.

```py
class C:
    def method(self) -> None:
        nonlocal __class__  # error: [invalid-syntax]

        def nested() -> None:
            nonlocal __class__  # error: [invalid-syntax]
            reveal_type(__class__)  # revealed: <class 'C'>
```

### Type alias annotation scopes

```toml
[environment]
python-version = "3.12"
```

```py
class C:
    # TODO: This should resolve to `C` without an error.
    type Alias = __class__  # error: [unresolved-reference]

    # TODO: This should resolve to `C` without an error.
    type GenericAlias[T] = __class__  # error: [unresolved-reference]
```

### Generic method bounds

```toml
[environment]
python-version = "3.12"
```

```py
class C:
    # TODO: The bound should resolve to `C` without an error.
    def method[T: __class__](self) -> None: ...  # error: [unresolved-reference]
```

### Deferred method annotations

Python 3.14 defers annotation evaluation, so ordinary method annotations can access the cell.

```toml
[environment]
python-version = "3.14"
```

```py
class C:
    def method(
        self,
        # TODO: This should resolve to `C` without an error.
        value: __class__,  # error: [unresolved-reference]
        # TODO: This should resolve to `C` without an error.
    ) -> __class__:  # error: [unresolved-reference]
        raise NotImplementedError
```
