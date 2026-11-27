def add1(x : int) -> int:
    return x + 1

def apply2(y : int) -> int:
    return add1(add1(y))

print(apply2(40))
