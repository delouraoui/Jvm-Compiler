def ack (n,m,e,k) =
   if n = 0 then ?(k)(e,m+1)
   else if m = 0 then ack (n-1,1,e,k)
   else ack (n,m-1,
    val bk = new [3] in
    bk[0]:=n;
    bk[1]:=e;
    bk[2]:=k;
    bk end, &aux)
   end
   end
def aux (bk,r) =
 val n = bk[0] in
 val e = bk[1] in
 val k = bk[2] in
 ack (n-1,r,e,k) end end end
def init(e,r) = r
val res = ack(3,4,new[0],&init)
/* answer: 125 */