import Cp
import Nat
import Rose

type Square = (Point, Side) 
type Side = Double
type Point = (Double, Double)

-- squares :: (Square, Int) -> Rose Square
squares = anaRose (func)

func (s, 0) = (s, [])
func (s, n) = (s, l)
    where l = generate8Squares(s, n)

generate8Squares (((p1,p2), l), n) = [(((p1,p2), l/3), n-1), (((p1+l/3, p2), l/3), n-1), (((p1+2*l/3, p2), l/3), n-1), (((p1, p2+l/3), l/3), n-1), (((p1+2*l/3, p2+l/3), l/3), n-1), (((p1, p2+2*l/3), l/3), n-1), (((p1+l/3, p2+2*l/3), l/3), n-1), (((p1+2*l/3, p2+2*l/3), l/3), n-1)]