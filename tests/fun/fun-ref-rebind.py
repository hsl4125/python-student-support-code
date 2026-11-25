def inc(x : int) -> int:
    return x + 1

def dec(x : int) -> int:
    return x - 1

def f(y : int) -> int:
    inc = dec
    return inc(y)

print(f(10))
