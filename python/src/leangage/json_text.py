"""The JSON text of a body as the tokens the generated functions take.

`lexemes` reads the text with `json` and lists its tokens in the order of the document: a number
as the text of its token, a member that comes twice as two members. It gives `None` for bytes
that `json` refuses: bytes that are not UTF-8, a text that is not JSON, `NaN` and `Infinity`, a
nesting deeper than the interpreter's stack takes (`RecursionError`), and a string with the
escape of a surrogate outside a pair. What the tokens mean is decided by the functions generated from
`lean/Leangage/Json/Lexemes.lean` and from the kernel's module.
"""

import json
from typing import Any

from leangage.json_lexemes import (
    Lexeme,
    Lexeme_arrClose,
    Lexeme_arrOpen,
    Lexeme_bool,
    Lexeme_key,
    Lexeme_null,
    Lexeme_number,
    Lexeme_objClose,
    Lexeme_objOpen,
    Lexeme_str,
)


class Number(str):
    """The text of a number token."""


class Members(list):
    """The members of an object, in the order of the document."""


def refuse(name: str) -> None:
    raise ValueError(name)


NULL = Lexeme_null()
TRUE = Lexeme_bool(b=True)
FALSE = Lexeme_bool(b=False)
ARR_OPEN = Lexeme_arrOpen()
ARR_CLOSE = Lexeme_arrClose()
OBJ_OPEN = Lexeme_objOpen()
OBJ_CLOSE = Lexeme_objClose()


def flatten(value: Any) -> list[Lexeme]:
    """The tokens of a value `json` read, without recursion on its nesting."""
    out: list[Lexeme] = []
    todo = [value]
    while todo:
        v = todo.pop()
        kind = type(v)
        if kind is str:
            v.encode()
            out.append(Lexeme_str(s=v))
        elif kind is Number:
            out.append(Lexeme_number(text=str(v)))
        elif kind is Members:
            out.append(OBJ_OPEN)
            todo.append(OBJ_CLOSE)
            for name, member in reversed(v):
                name.encode()
                todo.append(member)
                todo.append(Lexeme_key(s=name))
        elif kind is list:
            out.append(ARR_OPEN)
            todo.append(ARR_CLOSE)
            todo.extend(reversed(v))
        elif kind is bool:
            out.append(TRUE if v else FALSE)
        elif v is None:
            out.append(NULL)
        else:
            out.append(v)
    return out


def lexemes(data: bytes) -> list[Lexeme] | None:
    """The tokens of the JSON text `data`, or `None` for bytes `json` refuses."""
    try:
        return flatten(
            json.loads(
                data.decode(),
                object_pairs_hook=Members,
                parse_int=Number,
                parse_float=Number,
                parse_constant=refuse,
            )
        )
    except (ValueError, RecursionError):
        return None
