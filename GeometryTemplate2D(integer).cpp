#include <sstream>
#include <queue>
#include <stack>
#include <set>
#include <map>
#include <cstdio>
#include <cstdlib>
#include <cctype>
#include <complex>
#include <cmath>
#include <iostream>
#include <iomanip>
#include <string>
#include <utility>
#include <vector>
#include <algorithm>
#include <bitset>
#include <list>
#include <string.h>
#include <assert.h>
#include <time.h>

using namespace std;

#define SZ(x) ((int)x.size())
#define all(a) a.begin(),a.end()
#define allr(a) a.rbegin(),a.rend()
#define clrall(name,val) memset(name,(val),sizeof(name));
#define EPS 1e-9
#define ll long long
#define ull long long unsigned
#define SF scanf
#define PF printf
#define sf scanf
#define pf printf
#define psb(b) push_back((b))
#define ppb() pop_back()
#define oo (1<<28)
#define inf 0x3f3f3f3f
#define mp make_pair
#define mt make_tuple
#define get(a,b) get<b>(a)
#define fs first
#define sc second
#define Read freopen("in.txt","r",stdin)
#define Write freopen("out2.txt","w",stdout)
#define __ std::ios_base::sync_with_stdio (false),cin.tie(0),cout.tie(0)

ll MulModL(ll B,ll P,ll M) {    ll R=0; while(P>0)      { if((P&1ll)==1) { R=(R+B); if(R>=M) R-=M; } P>>=1ll; B=(B+B); if(B>=M) B-=M; } return R; }

ll MulModD(ll B, ll P,ll M) {   ll I=((long double)B*(long double)P/(long double)M);    ll R=B*P-M*I; R=(R%M+M)%M;  return R; }

ll BigMod(ll B,ll P,ll M) {     ll R=1; while(P>0)      { if(P%2==1) { R=(R*B)%M; } P/=2; B=(B*B)%M; } return R; } /// (B^P)%M

template<class T1> void deb(T1 e1){cout<<e1<<"\n";}
template<class T1,class T2> void deb(T1 e1,T2 e2){cout<<e1<<" "<<e2<<"\n";}
template<class T1,class T2,class T3> void deb(T1 e1,T2 e2,T3 e3){cout<<e1<<" "<<e2<<" "<<e3<<"\n";}
template<class T1,class T2,class T3,class T4> void deb(T1 e1,T2 e2,T3 e3,T4 e4){cout<<e1<<" "<<e2<<" "<<e3<<" "<<e4<<"\n";}
template<class T1,class T2,class T3,class T4,class T5> void deb(T1 e1,T2 e2,T3 e3,T4 e4,T5 e5){cout<<e1<<" "<<e2<<" "<<e3<<" "<<e4<<" "<<e5<<"\n";}
template<class T1,class T2,class T3,class T4,class T5,class T6> void deb(T1 e1,T2 e2,T3 e3,T4 e4,T5 e5,T6 e6){cout<<e1<<" "<<e2<<" "<<e3<<" "<<e4<<" "<<e5<<" "<<e6<<"\n";}
template<class T1,class T2,class T3,class T4,class T5,class T6,class T7> void deb(T1 e1,T2 e2,T3 e3,T4 e4,T5 e5,T6 e6,T7 e7){cout<<e1<<" "<<e2<<" "<<e3<<" "<<e4<<" "<<e5<<" "<<e6<<" "<<e7<<"\n";}

//int dx[]= {-1,-1,0,0,1,1};
//int dy[]= {-1,0,-1,1,0,1};
//int dx[]= {0,0,1,-1};/*4 side move*/
//int dy[]= {-1,1,0,0};/*4 side move*/
//int dx[]= {1,1,0,-1,-1,-1,0,1};/*8 side move*/
//int dy[]= {0,1,1,1,0,-1,-1,-1};/*8 side move*/
//int dx[]={1,1,2,2,-1,-1,-2,-2};/*night move*/
//int dy[]={2,-2,1,-1,2,-2,1,-1};/*night move*/

/**
//////////////////////////////////////////////
line segment intersection for ll value
*/
const double PI = acos(-1.0);
const double INF = 1e18;
typedef pair<double,double> pdd;
struct PT
{
    ll x,y;
    PT(){}
    PT(ll x,ll y):x(x),y(y){}
    void input()
    {
        sf("%lld %lld",&x,&y);
    }
    void output()
    {
        pf("%lld %lld\n",x,y);
    }
    bool operator < (const PT &p)  const
    {
        if(y==p.y) return x<p.x;
        return y<p.y;
    }
    bool operator == (const PT &p)  const
    {
        return mp(x,y)==mp(p.x,p.y);
    }
    bool operator != (const PT &p)  const
    {
        return mp(x,y)!=mp(p.x,p.y);
    }
    PT operator + (const PT &p)  const
    {
        return PT(x+p.x, y+p.y);
    }
    PT operator - (const PT &p)  const
    {
        return PT(x-p.x, y-p.y);
    }
    PT operator * (double c)     const
    {
        return PT(x*c,   y*c  );
    }
    PT operator / (double c)     const
    {
        return PT(x/c,   y/c  );
    }
};

double Distance(PT a,PT b)
{
    PT p=a-b;
    return sqrt(p.x*p.x+p.y*p.y);
}

ll dot(PT p, PT q)
{
    return p.x*q.x+p.y*q.y;
}
ll cross(PT p, PT q)
{
    return p.x*q.y-p.y*q.x;
}
///***
bool areLinesSame(PT a, PT b, PT c, PT d)
{
    if(cross(a-c,c-d)==0 && cross(b-c,c-d)==0) return true;
    return false;
}
///***
bool areLinesParallel(PT a, PT b, PT c, PT d)
{
    if(cross(a-b,c-d)==0) return true;
    return false;
}

// compute intersection of line passing through a and b
// with line passing through c and d, assuming that unique
// intersection exists; for segment intersection, check if
// segments intersect first
//void ComputeLineIntersection(PT a, PT b, PT c, PT d,pdd &ret)
//{
//    b=b-a;
//    d=c-d;
//    c=c-a;
//    double h=(double)cross(c, d)/(double)cross(b, d);
//    ret.xx=(double) a.x + (double) b.x * h;
//    ret.yy=(double) a.y + (double) b.y * h;
//    return ;
//}

void ComputeLineIntersection(PT a, PT b, PT c, PT d,pdd &ret)
{
    double a1,b1,c1,a2,b2,c2;
    a1 = a.y - b.y;
    b1 = b.x - a.x;
    c1 = cross(a, b);
    a2 = c.y - d.y;
    b2 = d.x - c.x;
    c2 = cross(c, d);
    double D = a1 * b2 - a2 * b1;
    ret=mp((b1 * c2 - b2 * c1) / D,(c1 * a2 - c2 * a1) / D);
    return ;
}

bool onsegment(PT a,PT b,PT c){
    return ( min(a.x,b.x)<=c.x && c.x<=max(a.x,b.x) && min(a.y,b.y)<=c.y && c.y<=max(a.y,b.y) ) ;
}
bool isSegmentIntersect(PT p1,PT p2,PT p3,PT p4)
{
    ll d1,d2,d3,d4;

    d1 = cross(p4-p3,p1-p3);
    d2 = cross(p4-p3,p2-p3);
    d3 = cross(p2-p1,p3-p1);
    d4 = cross(p2-p1,p4-p1);

    int s1,s2,s3,s4;
    s1=d1==0?0:d1<0?-1:1;
    s2=d2==0?0:d2<0?-1:1;
    s3=d3==0?0:d3<0?-1:1;
    s4=d4==0?0:d4<0?-1:1;

    if(s1*s2<0 && s3*s4<0)  return true;
    if(!d1 && onsegment(p3,p4,p1))  return true;
    if(!d2 && onsegment(p3,p4,p2))  return true;
    if(!d3 && onsegment(p1,p2,p3))  return true;
    if(!d4 && onsegment(p1,p2,p4))  return true;

    return false;
}

bool ComputeLineSegmentIntersection(PT a, PT b, PT c, PT d,pdd &ret)
{
    if(!isSegmentIntersect(a,b,c,d)) return false;
    double a1,b1,c1,a2,b2,c2;
    a1 = a.y - b.y;
    b1 = b.x - a.x;
    c1 = cross(a, b);
    a2 = c.y - d.y;
    b2 = d.x - c.x;
    c2 = cross(c, d);
    double D = a1 * b2 - a2 * b1;
    ret=mp((b1 * c2 - b2 * c1) / D,(c1 * a2 - c2 * a1) / D);
    return true;
}

bool compAng(const PT& a,const PT& b)
{
    ll c=cross(a,b);
    if(c!=0) return c>0;
    ll d1=dot(a,a),d2=dot(b,b);
    return d1>d2;
}
/**
convex_hull : including collinear points
counterclockwise
*/
void ConvexHull(vector<PT>& poly,vector<PT>& ret)
{
    int n=SZ(poly);
    if(n==0) return ;
    sort(all(poly));
    poly.resize(distance(poly.begin(),unique(all(poly))));
    n=SZ(poly);
    PT fpoint = poly[0];
    for(int i=0;i<n;i++)
    {
        poly[i]=poly[i]-fpoint;
    }
    stack<PT> S;
    PT f;
    PT p1,p2,p3;
    if(n>2)
    {
        sort(poly.begin()+1,poly.end(),compAng);
        bool ok;
        ll c;
        S.push(poly[0]);
        S.push(poly[1]);
        for(int i=2;i<=n;i++)
        {
            p3=poly[i%n];
            ok=(i!=n);
            do{
                p2=S.top(); S.pop();
                p1=S.top();
                S.push(p2);
                c=cross(p2-p1,p3-p1);
                if(c<0)
                {
                    if(SZ(S)>2) S.pop();
                    else break;
                }
                else if(c==0)
                {
                    ll d12=dot(p2-p1,p2-p1),d13=dot(p3-p1,p3-p1);
                    if(d13<=d12) ok=false;
                    else
                    {
                        if(SZ(S)>=2) S.pop();
                    }
                    break;
                }
                else break;
            }while(SZ(S)>=2);
            if(ok) S.push(p3);
        }
        while(!S.empty()){
            ret.psb(S.top());
            S.pop();
        }
        reverse(all(ret));
    }
    else
    {
        ret=poly;
    }
    n=SZ(ret);
    for(int i=0;i<n;i++)
    {
        ret[i]=ret[i]+fpoint;
    }
    return ;
}

int main()
{
    #ifdef MAHDI
//    Read;
//    Write;
    #endif // MAHDI
    vector<PT> poly,cpoly;
    poly.psb(PT(5,7));
    poly.psb(PT(1,9));
    poly.psb(PT(3,6));
    poly.psb(PT(15,7));
    poly.psb(PT(27,8));
    poly.psb(PT(5,9));

//    poly.psb(PT(0,0));
//    poly.psb(PT(0,1));
//    poly.psb(PT(0,2));
//    poly.psb(PT(0,3));
//    poly.psb(PT(0,4));
//    poly.psb(PT(0,5));
    ConvexHull(poly,cpoly);
    for(int i=0;i<SZ(cpoly);i++)
    {
        cpoly[i].output();
    }
    return 0;
}



/**
100
4 3
0 1
0 2
0 3
0 4
*/











