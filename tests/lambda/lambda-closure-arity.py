def make() -> Callable[[int], int]:
    return lambda y: y + 1

g: Callable[[int], int] = make()
print(arity(g) + g(40))
