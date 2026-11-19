x = 5
if 1 < 2:
    y = 100
else:
    y = 200
if x < 2:
    z = 1000
else:
    z = 0
print(y + z + (1 + 2 + 3 + 4) + ((1 - 2) - 3) + (-(-5))
      + (1 if 1 < 2 else 0)
      + (1 if not (1 < 2) else 0)
      + (1 if (True and 1 < 2) else 0)
      + (1 if (False or 1 < 2) else 0))
