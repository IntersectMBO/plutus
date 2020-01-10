(declare-datatypes
 ()
 ((Slot
   (mk-slot
    (get-slot Int)))))

(declare-datatypes
 ()
 ((SlotInterval
   (mk-slot-interval
    (slot-left Slot)
    (slot-right Slot)))))

(declare-datatypes
 ()
 ((IntervalResult (interval-trimmed (get-min-slot Slot))
                  (invalid-interval)
                  (interval-in-past))))

(define-fun max
  ((a Int) (b Int))
  Int
  (ite (> a b)
       a
       b))

(define-fun valid-interval
  ((slot-interval SlotInterval))
  Bool
  (<= (get-slot (slot-left slot-interval))
      (get-slot (slot-right slot-interval))))

(define-fun above
  ((slot Slot) (slot-interval SlotInterval))
  Bool
  (> (get-slot slot)
     (get-slot (slot-right slot-interval))))

(define-fun fix-interval
  ((slot-interval SlotInterval)
   (min-slot Slot))
  IntervalResult
  (ite (valid-interval slot-interval)
       (ite (above min-slot slot-interval)
            interval-in-past
            (interval-trimmed (mk-slot (max 
                                        (get-slot min-slot) 
                                        (get-slot (slot-right slot-interval))))))
       invalid-interval))

(define-fun rec-fun
  ((n Int))
  Int
  (ite (>= 10 n)
    0
    (rec-fun (+ 1 n)))
  )