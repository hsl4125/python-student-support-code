def make(x: int) -> Callable[[int], Callable[[int], int]]:
    return lambda y: (lambda z: x + y + z)

print(make(1)(2)(39))
