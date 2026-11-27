def f(a: int, b: int, c: int, d: int, e: int, g: int, h: int) -> Callable[[int], int]:
    return lambda x: a + b + c + d + e + g + h + x

print(f(1, 2, 3, 4, 5, 6, 7)(0))
