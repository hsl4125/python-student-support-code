def fact(n : int, acc : int) -> int:
    if n == 0:
        return acc
    return fact(n - 1, acc * n)

print(fact(5, 1))
