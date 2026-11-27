y = input_int()
add1 : Callable[[int], int] = lambda x: x + 1
g : Callable[[int], int] = lambda x: x + y
h : Callable[[int], int] = add1 if input_int() == 0 else g
print(h(41))
