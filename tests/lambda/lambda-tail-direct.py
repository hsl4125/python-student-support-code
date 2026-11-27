def tail_sum(n : int, acc : int) -> int:
    if n == 0:
        return acc
    return tail_sum(n - 1, acc + n)

print(tail_sum(3, 0) + 36)
