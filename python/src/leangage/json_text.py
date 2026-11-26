"""The JSON text of a body as the tokens the generated functions take.

`tokens` reads the text with `json` and gives its tokens in the order of the document as a
`Tokens`: one character for the kind of each token (`{`, `}`, `[`, `]`, `n`, `t`, `f`, `#` for a
number, `s` for a string, `k` for a key) and the texts of the numbers, the strings and the keys;
a member that comes twice is two members. It gives `None` for bytes that `json` refuses: bytes
that are not UTF-8, a text that is not JSON, `NaN` and `Infinity`, a nesting deeper than the
interpreter's stack takes (`RecursionError`), and a string with the escape of a surrogate outside
a pair. What the tokens mean is decided by the functions generated from
`lean/Leangage/Json/Lexemes.lean` and from the kernel's module.
"""

import json

from leangage.json_lexemes import Tokens


class Number(str):
    """The text of a number token."""


class Members(list):
    """The members of an object, each a pair, in the order of the document."""


class Close(str):
    """The kind of the token that closes an array or an object."""


def refuse(name: str) -> None:
    raise ValueError(name)


OBJ_CLOSE = Close("}")
ARR_CLOSE = Close("]")
DECODER = json.JSONDecoder(
    object_pairs_hook=Members,
    parse_int=Number,
    parse_float=Number,
    parse_constant=refuse,
)


def tokens(data: bytes) -> Tokens | None:
    """The tokens of the JSON text `data`, or `None` for bytes `json` refuses."""
    try:
        kinds: list[str] = []
        texts: list[str] = []
        todo = [DECODER.decode(data.decode())]
        while todo:
            v = todo.pop()
            kind = type(v)
            if kind is tuple:
                kinds.append("k")
                texts.append(v[0])
                todo.append(v[1])
            elif kind is str:
                kinds.append("s")
                texts.append(v)
            elif kind is Number:
                kinds.append("#")
                texts.append(v)
            elif kind is Close:
                kinds.append(v)
            elif kind is Members:
                kinds.append("{")
                todo.append(OBJ_CLOSE)
                todo.extend(reversed(v))
            elif kind is list:
                kinds.append("[")
                todo.append(ARR_CLOSE)
                todo.extend(reversed(v))
            elif kind is bool:
                kinds.append("t" if v else "f")
            else:
                kinds.append("n")
        "".join(texts).encode()
        return Tokens(kinds="".join(kinds), texts=texts)
    except (ValueError, RecursionError):
        return None
