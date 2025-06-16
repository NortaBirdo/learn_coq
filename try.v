Definition andb (a b : bool): bool := 
 match a, b with
| true, true => true
| true, false => false
| false, false => false
| false, true => false
end.