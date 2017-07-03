/* fact in Kontix (after translation to continuation-passing-style) */
def fact(x,k,e) = if x = 0 then ?(k)(e,1) else
 fact(x-1,&aux,
  val bk = new[3] in
  bk[0]:=x;
  bk[1]:=k;
  bk[2]:=e;
  bk end) end
def aux(bk,r) =
 val n = bk[0] in
 val k = bk[1] in
 val e = bk[2] in
 ?(k)(e,r*n) end end end
def init(e,r) = r
val res = fact(10,&init,new[0])
/* answer: 3628800 */