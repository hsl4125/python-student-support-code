def inc(x : int) -> int:
    return x + 1

def twice(f : Callable[[int], int], x : int) -> int:
    return f(f(x))

print(twice(inc, 40))
