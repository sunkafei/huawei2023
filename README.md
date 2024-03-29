# 决赛代码解析
## 先求出一个较优的可行解
- 首先对于每一个业务，假设该业务要求在s到t之间建立k条路径。那么我们就循环k次，依次添加一条路径，我们的路径搜索算法按顺序考虑下面的条件：
  1. 非必要不加边，如果必须加边，那么加的边应当越少越好。
  2. 走s到t的最短路。
  3. 往通道编号小的通道里塞。
  
  通过对BFS算法进行改进，上述算法可以在O(n)时间内实现！

## 删掉不必要的新加边
- 在求出可行解的基础上，我们枚举每一条新加的边，把这条边删除掉，此时原方案不再是合法解。对此，我们把经过这条边所有业务删除掉，然后用前面介绍的算法尝试重新插入进来，如果能完成重新插入，那么就可以删除这条边，否则回退到删除之前的方案。

## 构造同构解，进行再删除
- 在枚举完一遍所有新添加的边是否可删除之后，再枚举一遍是没有意义的，因为上一遍没有删除的边再循环一遍也会被删除。
- 对此，我们考虑构造出同构解，也就是要构造一组新的解，使得它不比原来的解差，而且两个解之间尽可能的不相同，这样对这个新的解再进行上一步的枚举删边，就可能会删除掉一些新的边，使得解进一步变好。
- 具体的，我们枚举每一个业务，将它从方案中删除，然后重新插入进来，与之前不同的是，这一次插入会将插入算法的第3条改成往通道编号尽可能大的通道里塞。这样循环一次后会得到一个焕然一新的解，然后在进行一遍上一步的循环枚举删边。

## 一直优化，直到时间限制为止
- 在第一次构造新的解的时候，我们把也业务往通道编号尽可能大的通道里塞。下一次的时候就往通道编号小的通道里塞，再下一次又是大编号优先，如此往复，直到时间限制。
- 可以把整个过程形象的想象成一个转漏斗的过程：
  - 求出来一个解，然后枚举删边。
  - 把漏斗倒过来（把业务挪到大编号端），枚举删边。 
  - 再把漏斗倒过来（把业务挪到小编号端），枚举删边。 
  - 再把漏斗倒过来（把业务挪到大编号端），枚举删边。 
  - 再把漏斗倒过来（把业务挪到小编号端），枚举删边。 
  - ......
  
  在每次转漏斗的过程中，业务会被一定程度的shuffle，然后在枚举删边的时候就会删除掉一些新边。

  随着时间推移，解会变得越来越好，甚至接近最优解。

## 一些其它说明
- 放大器对最终结果的相对影响非常小，我们有一些针对放大器的优化，鉴于不是重点，就不介绍了。
- 在算法实现的过程中，我们使用了非常多的优化技巧来优化算法的性能（常数优化），在此也不再赘述。
