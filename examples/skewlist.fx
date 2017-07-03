def nil () =
  val bk = new [1] in
  bk[0]:=0; /* tag */
  bk end

def cons (x,t,l) =
  val bk = new [4] in
  bk[0]:=1; /* tag */
  bk[1]:=x;
  bk[2]:=t;
  bk[3]:=l;
  bk end

/* Definition des arbres */
def leaf (a) =
  val bk = new [2] in
  bk[0]:=0; /* tag */
  bk[1]:=a;
  bk end

def node (a,g,d) =
  val bk = new [4] in
  bk[0]:=1; /* tag */
  bk[1]:=a; /**value**/                  
  bk[2]:=g;
  bk[3]:=d;
  bk end


/** Debut skew list **/
val empty = nil ()
                
def is_empty (a) =
  if a[0]  = 0 then true
  else false end
         
def scons(x,l) = 
  if l[0] = 1 then
     val w1    = l[1]  in
     val t1    = l[2]  in
     val succ  = l[3]  in
     if succ[0] = 1 then
       val w2    = succ[1] in
       val t2    = succ[2] in
       if w1 = w2 then
         cons(1+w1+w2,node(x,t1,t2),succ[3])
       else cons(1,leaf(x),l) end end end 
     else cons(1,leaf(x),l) end end end end 
else cons(1,leaf(x),l) end

def head(l) = 
  if l[0] = 1 then
   val t = l[2]  in
   t[1] end 
else /* assert false **/ 0 end

def tail(l) = 
  if l[0] = 1 then
   val t = t[2]  in
   if t[0] = 0 then l[3]    
   else
    val w =  l[1] in 
    val t1 = t[1] in
    val t2 = t[2] in
    cons (w/2,t1,cons(w/2,t2,l[1])) end end end end end
else /* assert false **/ 0 end

def lookup_tree(i,w,t) =
  if t[0] = 0 then
    if i = 0 then t[1]
    else 0 end
  else
    if i = 0 then t[1]
    else
      if i -1 < (w/2) then lookup_tree((i - 1),(w / 2),t[2])
      else lookup_tree((i - 1 - w / 2),(w / 2),t[3]) end end end

def lookup(i,l) =
  if l[0] = 0 then /** assert false **/ 0
  else
    val w = l[1] in    
    if i < w then lookup_tree(i,w,l[2])
    else lookup(i-w,l[3]) end end end

def update_tree(i,v,w,t) =
  if t[0] = 0 then
    if i = 0 then leaf(v)
    else 0 end
  else
    if i = 0 then node(v,t[2],t[3])
    else
      if i -1 < (w/2) then node(t[1],(update_tree (i-1, v, (w/2),t[2])),t[3])
      else node(t[1],t[2],(update_tree (i-1- w / 2, v, (w/2),t[3]))) end end end

def update(i,v,l) =
  if l[0] = 0 then /** assert false **/ 0
  else
    val w = l[1] in    
    if i < w then cons(w,(update_tree(i,v,w,l[2])),l[3])
    else cons(w,l[2],(update(i-w,v,l[3]))) end end end

val _ =
  val l = scons(109,scons(108,scons(107,scons(106,scons(105,scons(104,scons(103,scons(102,scons(101,scons(100,nil ())))))))))) in
      /** resultat 109 **/
  val h1 = head(l) in
      /** resultat 109 **/
  val h2 = lookup(0,l) in
      /** resultat 108 **/
  val h3 = lookup(1,l) in
    /** resultat 107 **/
  val h4 = lookup(2,l) in
      /** resultat 106 **/
  val h5 = lookup(3,l) in
      /** resultat 105 **/
  val h6 = lookup(4,l) in
      /** resultat 104 **/
  val h7 = lookup(5,l) in
      /** resultat 103 **/
  val h8 = lookup(6,l) in
      /** resultat 102 **/
  val h9 = lookup(7,l) in
      /** resultat 101 **/
  val h10 = lookup(8,l) in
      /** resultat 100 **/
  val h11 = lookup(9,l) in
      /** resultat 99 **/
  val up0 = update(0,99,l) in
  val up1 = lookup(9,up0) in
  up1
end end end end end end end end end end end end end end
