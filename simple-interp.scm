(defrel (evalo expr val)
  (eval-expro expr '() val))

(defrel (eval-expro expr env val)
  (conde
    ((fresh (rator rand x body env^ a)
       (== `(,rator ,rand) expr)
       (eval-expro rator env `(closure ,x ,body ,env^))
       (eval-expro rand env a)
       (eval-expro body `((,x . ,a) . ,env^) val)))
    ((fresh (x body)
       (== `(lambda (,x) ,body) expr)
       (symbolo x)
       (== `(closure ,x ,body ,env) val)
       (not-in-envo 'lambda env)))
    ((symbolo expr) (lookupo expr env val))))

(defrel (not-in-envo x env)
  (conde
    ((== '() env))
    ((fresh (y v rest)
       (== `((,y . ,v) . ,rest) env)
       (=/= y x)
       (not-in-envo x rest)))))

(defrel (lookupo x env t)
  (conde
    ((fresh (y v rest)
       (== `((,y . ,v) . ,rest) env) (== y x)
       (== v t)))
    ((fresh (y v rest)
       (== `((,y . ,v) . ,rest) env) (=/= y x)
       (lookupo x rest t)))))
