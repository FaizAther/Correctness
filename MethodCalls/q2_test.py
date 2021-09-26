

def commputePosRec(num, den):
  #print("nu={}--REC-START--de={}\n".format(num, den))
  if num == 0 and den == 0:
    return 0
  elif num == 1 and den == 1:
    return 1
  else:
    if (num < den): # left
      num, den = num, den - num
      pos = commputePosRec(num, den)
      pos *= 2
      #print("left\n")
    else: # right
      num, den = num - den, den
      pos = commputePosRec(num, den)
      pos = (pos * 2) + 1
      #print("right\n")

  #print("nu={}--REC-END--de={}--pos={}\n".format(num, den, pos))
  return pos


if __name__ == "__main__":
  for i in range(1,10):
    for j in range(1,10):
      import math
      if (i != j and math.gcd(i, j) == 1):
        num, den = i, j
        print(num, den)
        t2 = commputePosRec(num, den)
        print(t2)
  num, den = 3, 8
  t2 = commputePosRec(num, den)
  print(t2)


