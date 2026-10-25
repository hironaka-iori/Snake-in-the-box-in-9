from survey import p,HERE
p.DIRS=[0,1,2,0]
p.solve('four-step-return-sum4',[21]*3,seconds=8,joint=([1,3],4))
p.solve('four-step-return-sum5',[21]*3,seconds=8,joint=([1,3],5))
