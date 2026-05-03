# Pydantic

```toml
[environment]
python-version = "3.12"
python-platform = "linux"

[project]
dependencies = ["pydantic==2.12.2"]
```

## Basic model

```py
from pydantic import BaseModel

class User(BaseModel):
    id: int
    name: str

reveal_type(User.__init__)  # revealed: (self: User, *, id: int, name: str) -> None

user = User(id=1, name="John Doe")
reveal_type(user.id)  # revealed: int
reveal_type(user.name)  # revealed: str

# error: [missing-argument] "No argument provided for required parameter `name`"
invalid_user = User(id=2)
```

## Usage of `Field`

```py
from pydantic import BaseModel, Field

class Product(BaseModel):
    id: int = Field(init=False)
    name: str = Field(..., kw_only=False, min_length=1)
    internal_price_cent: int = Field(..., gt=0, alias="price_cent")

reveal_type(Product.__init__)  # revealed: (self: Product, name: str = ..., *, price_cent: int = ...) -> None

product = Product("Laptop", price_cent=999_00)

reveal_type(product.id)  # revealed: int
reveal_type(product.name)  # revealed: str
reveal_type(product.internal_price_cent)  # revealed: int
```

## Inherited `ModelMetaclass`

Pydantic's metaclass-based `@dataclass_transform` metadata should continue to apply when a custom
metaclass inherits from `ModelMetaclass`.

```py
from pydantic import BaseModel
from pydantic._internal._model_construction import ModelMetaclass

class RegistryMeta(ModelMetaclass): ...

class User(BaseModel, metaclass=RegistryMeta):
    name: str
    age: int = 0

reveal_type(User.__init__)  # revealed: (self: User, *, name: str, age: int = 0) -> None

User(name="alice")
User(name="alice", age=1)

# error: [missing-argument]
User()

# error: [unknown-argument]
User(name="alice", extra=1)
```

## `Field` alias with a default value

Alias-based constructor synthesis should also work on the defaulted `Field(...)` overloads:

```py
from pydantic import BaseModel, Field

class Result(BaseModel):
    meta: dict[str, object] | None = Field(alias="_meta", default=None)

reveal_type(Result.__init__)  # revealed: (self: Result, *, _meta: dict[str, object] | None = None) -> None

Result(_meta=None)
```

## `Field` alias via module attribute

Alias-based constructor synthesis should also work when `Field` is referenced through the `pydantic`
module:

```py
import pydantic

class Result(pydantic.BaseModel):
    meta: dict[str, object] | None = pydantic.Field(alias="_meta", default=None)

reveal_type(Result.__init__)  # revealed: (self: Result, *, _meta: dict[str, object] | None = None) -> None

Result(_meta=None)
```

## `Field` literal defaults should satisfy literal-union annotations

Explicit literal defaults should remain precise when Pydantic `Field(...)` is used as a field
specifier:

```py
from typing import Literal

from pydantic import BaseModel, Field

class Card(BaseModel):
    header_image_type: Literal["ai", "image_search"] = Field(default="ai")

reveal_type(Card.__init__)  # revealed: (self: Card, *, header_image_type: Literal["ai", "image_search"] = "ai") -> None

card = Card()
reveal_type(card.header_image_type)  # revealed: Literal["ai", "image_search"]
```

## `Field` default factory callable overloads

Pydantic accepts both zero-argument and validated-data-aware factories. When the selected factory is
a zero-argument lambda, the lambda body should still use the declared field type as context:

```py
from pydantic import BaseModel, Field

class Defaults(BaseModel):
    values: list[int | str] = Field(default_factory=lambda: [1])

reveal_type(Defaults.__init__)  # revealed: (self: Defaults, *, values: list[int | str] = ...) -> None

defaults = Defaults()
reveal_type(defaults.values)  # revealed: list[int | str]
```

## Discriminated unions with enum-member tags

Enum-valued discriminators should narrow the containing Pydantic union just like string-valued
discriminators:

```py
from enum import Enum
from typing import Annotated, Literal

from pydantic import BaseModel, Field

class Kind(Enum):
    TEXT = 1
    IMAGE = 2

class Text(BaseModel):
    kind: Literal[Kind.TEXT] = Kind.TEXT
    parts: list[str]

class Image(BaseModel):
    kind: Literal[Kind.IMAGE] = Kind.IMAGE
    width: int

Tagged = Annotated[Text | Image, Field(discriminator="kind")]

def _(content: Tagged):
    if content.kind == Kind.TEXT:
        reveal_type(content)  # revealed: Text
        reveal_type(content.parts)  # revealed: list[str]
    else:
        reveal_type(content)  # revealed: Image
```

## Validator and serializer decorators with explicit `@classmethod`

Pydantic [recommends](https://docs.pydantic.dev/latest/concepts/validators/#class-validators) using
an explicit `@classmethod` decorator below `@field_validator` / `@model_validator(mode="before")` /
`@field_serializer` to get proper type checking. The first parameter should be inferred as
`type[Self]`. ty does not support recognizing these functions as *implicit* class methods, so the
`@classmethod` decorator is required for correct type inference.

```py
from pydantic import BaseModel, field_validator, model_validator, field_serializer

class User(BaseModel):
    name: str

    @field_validator("name")
    @classmethod
    def validate_name(cls, v: str) -> str:
        reveal_type(cls)  # revealed: type[Self@validate_name]
        return v.strip()

    @model_validator(mode="before")
    @classmethod
    def validate_model_before(cls, values: dict) -> dict:
        reveal_type(cls)  # revealed: type[Self@validate_model_before]
        return values

    @field_serializer("name")
    @classmethod
    def serialize_name(cls, v: str) -> str:
        reveal_type(cls)  # revealed: type[Self@serialize_name]
        return v.upper()

    # No @classmethod for "after" validators: the first parameter should be inferred as "Self"
    @model_validator(mode="after")
    def validate_model_after(self) -> "User":
        reveal_type(self)  # revealed: Self@validate_model_after
        return self
```
