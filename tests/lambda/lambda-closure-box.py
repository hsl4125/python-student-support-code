def f(x: int) -> Callable[[int], int]:
    y = 4
    return lambda z: x + y + z

g: Callable[[int], int] = f(5)
h: Callable[[int], int] = f(3)
print(g(11) + h(15))
