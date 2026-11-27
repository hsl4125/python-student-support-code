def inc(x : int) -> int:
    return x + 1

def apply(inc : Callable[[int], int], x : int) -> int:
    return inc(x)

print(apply(inc, 41))
