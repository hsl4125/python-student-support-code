def f(x: int) -> Callable[[int], int]:
    y = 2
    z = 3
    return lambda a: a + x + y + z

print(f(0)(37))
