ll n;
ll N[60], res;
vector <ll> clique;

void BronKerbosch(ll n, ll R, ll P, ll X) // initial call (0,(1LL<<n) - 1,0)
{
    if (P == 0LL && X == 0LL)
    {
        ll t = 0;
        vector <ll> v;
        for (ll i = 0; i < n; i++)
            if ((1ll << i) & R)
                t ++, v.pb (i + 1);
        if (t > res)
        {
            res = t;
            clique = v;
        }
        res = max(res, t);
        return;
    }
    ll u = 0;
    while (!((1ll<<u) & (P|X)))
        u ++;
    for (ll v = 0; v < n; v++)
    {
        if (((1ll << v) & P) && !((1ll << v) & N[u]))
        {
            BronKerbosch(n, R | (1ll << v), P & N[v], X & N[v]);
            P -= (1ll << v);
            X |= (1ll << v);
        }
    }
}
