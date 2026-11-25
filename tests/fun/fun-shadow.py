def inc(x : int) -> int:
    return x + 1

def f(inc : int) -> int:
    return inc + 1

print(f(1) + inc(1))
