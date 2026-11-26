def positive(x : int) -> bool:
    return x > 0

def check(x : int) -> int:
    if positive(x):
        return 1
    return 0

print(check(5) * 10 + check(-1))
