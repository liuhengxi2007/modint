#include<cstdio>
#include<algorithm>
#include<array>
typedef unsigned uint;
typedef unsigned long long ull;
typedef __uint128_t u128;
constexpr uint MOD=1000000007;
namespace modint
{
	using namespace std;
	constexpr ull INV=-1ull/MOD;
	constexpr ull div(ull a){return a/MOD+!!(a%MOD);}
	constexpr ull width(array<ull,2> a){return div(a[0])+div(a[1]);}
	constexpr bool fit(array<u128,2> a)
	{
		constexpr ull W_LIM=-1ull/MOD;
		if(a[0]>-1ull||a[1]>-1ull)return false;
		return width({(ull)a[0],(ull)a[1]})<=W_LIM;
	}
	constexpr array<ull,2> csub(array<ull,2> a){return {((width(a)+1)>>1)*MOD,0};}
	constexpr array<ull,2> barrett([[maybe_unused]]array<ull,2> a){return {2*MOD,0};}
	template<ull A,ull B>ull csub(ull x)
	{
		constexpr ull a=div(A),b=div(B),c=((a+b)>>1)*MOD;
		if constexpr(b*MOD==c)return min(x,x+c);
		x+=b*MOD;
		return min(x,x-c);
	}
	template<ull A,ull B>constexpr ull barrett(ull x)
	{
		constexpr ull b=div(B);
		x+=b*MOD;
		return x-=(ull)(((u128)x*INV>>64)*MOD);
	}
	constexpr pair<array<ull,2>,array<int,2>> get_range(int o,array<ull,2> a,array<ull,2> b)
	{
		array<u128,2> c{};
		array<int,2> t{};
		while(true)
		{
			if(o==0)c={a[1],a[0]};
			if(o==1)c={(u128)a[0]+b[0],(u128)a[1]+b[1]};
			if(o==2)c={(u128)a[0]+b[1],(u128)a[1]+b[0]};
			if(o==3)c={max((u128)a[0]*b[0],(u128)a[1]*b[1]),max((u128)a[0]*b[1],(u128)a[1]*b[0])};
			if(fit(c))break;
			if(o==0)throw;
			if(o==1||o==2)
			{
				if(width(a)>=width(b))a=csub(a),t[0]=1;
				else b=csub(b),t[1]=1;
			}
			if(o==3)
			{
				if(width(a)>=width(b))a=barrett(a),t[0]=2;
				else b=barrett(b),t[1]=2;
			}
		}
		return {{(ull)c[0],(ull)c[1]},t};
	}
	template<uint A>
	struct mint_const
	{
		static constexpr bool is_mint_expr=true;
		static constexpr array<ull,2> V{A,0};
		static constexpr uint a=A;
	};
	namespace literal
	{
		template<uint s,char... c>struct parser;
		template<uint s,char c,char... r>struct parser<s,c,r...>
		{
			static_assert(c>='0'&&c<='9',"Non-digit character in literal");
			static constexpr uint v=parser<(s*10ull+(c-'0'))%MOD,r...>::v;
		};
		template<uint s>struct parser<s>{static constexpr uint v=s;};
		template<char... c>constexpr auto operator""_m(){return mint_const<parser<0,c...>::v>();}
	}
	struct mint;
	template<int O,typename A,typename B>
	struct mint_expr
	{
		static constexpr bool is_mint_expr=A::is_mint_expr&&B::is_mint_expr;
		static constexpr array<ull,2> V=get_range(O,A::V,B::V).first;
		enable_if_t<is_mint_expr,ull> a;
		uint to_mint_uint()
		{
			constexpr ull d0=div(V[0]),d1=div(V[1]);
			if constexpr(d0+d1<=1)return (uint)(a+d0*MOD);
			if constexpr(d0+d1<=2)return (uint)csub<V[0],V[1]>(a);
			return (uint)barrett<V[0],V[1]>(a);
		}
		mint to_mint();
	};
	template<int O,typename A,typename B>void prepare(A &a,B &b)
	{
		constexpr array<int,2> t=get_range(O,A::V,B::V).second;
		if constexpr(t[0]==1)a.a=csub<A::V[0],A::V[1]>(a.a);
		if constexpr(t[0]==2)a.a=barrett<A::V[0],A::V[1]>(a.a);
		if constexpr(t[1]==1)b.a=csub<B::V[0],B::V[1]>(b.a);
		if constexpr(t[1]==2)b.a=barrett<B::V[0],B::V[1]>(b.a);
	}
	template<typename A>enable_if_t<A::is_mint_expr,A> operator+(A a)
	{
		return a;
	}
	template<typename A>enable_if_t<A::is_mint_expr,mint_expr<0,A,mint_const<0>>> operator-(A a)
	{
		return {-(ull)a.a};
	}
	template<typename A,typename B>enable_if_t<A::is_mint_expr&&B::is_mint_expr,mint_expr<1,A,B>> operator+(A a,B b)
	{
		prepare<1,A,B>(a,b);
		return {(ull)a.a+b.a};
	}
	template<typename A,typename B>enable_if_t<A::is_mint_expr&&B::is_mint_expr,mint_expr<2,A,B>> operator-(A a,B b)
	{
		prepare<2,A,B>(a,b);
		return {(ull)a.a-b.a};
	}
	template<typename A,typename B>enable_if_t<A::is_mint_expr&&B::is_mint_expr,mint_expr<3,A,B>> operator*(A a,B b)
	{
		prepare<3,A,B>(a,b);
		return {(ull)a.a*b.a};
	}
	struct mint
	{
		static constexpr bool is_mint_expr=true;
		static constexpr array<ull,2> V{2*MOD,0};
		uint a;
		mint():a(){}
		template<uint v>mint(mint_const<v>):a(v){}
		template<int O,typename A,typename B>mint(mint_expr<O,A,B> b):a(b.to_mint_uint()){}
		uint raw()const{return a;}
		uint to_int()const{return a==2*MOD?0:min(a,a-MOD);}
	};
	template<int O,typename A,typename B>
	mint mint_expr<O,A,B>::to_mint(){return mint(*this);}
}
using modint::literal::operator""_m;
using modint::mint;
uint func(uint a,uint b,uint c)
{
	return (uint)((a+(ull)b*(MOD-c))%MOD);
}
mint func(mint a,mint b,mint c)
{
	return a+b*-c;
}
constexpr int N=1e8;
void test0()
{
	uint a=1235,b=2134,c=9442;
	for(int i=0;i<N;++i)
	{
		a=func(a,b,c);
		b=func(b,c,a);
		c=func(c,a,b);
	}
	printf("%d %d %d\n",a,b,c);
}
void test1()
{
	mint a=1235_m,b=2134_m,c=9442_m;
	for(int i=0;i<N;++i)
	{
		a=func(a,b,c);
		b=func(b,c,a);
		c=func(c,a,b);
	}
	printf("%d %d %d\n",a.to_int(),b.to_int(),c.to_int());
}
int main()
{
	test1();
	return 0;
}
