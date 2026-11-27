def f(x: int) -> Callable[[int], int]:
    return lambda y: x + y

g: Callable[[int], int] = f(5)
print(g(37))
