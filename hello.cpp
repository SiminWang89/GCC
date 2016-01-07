#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string>
#include <iostream>
#include <gsl/gsl_math.h>
#include <gsl/gsl_combination.h>
#include <gsl/gsl_complex.h>
#include <gsl/gsl_complex_math.h>
#include <gsl/gsl_block.h>
#include <gsl/gsl_vector.h>
#include <gsl/gsl_matrix.h>
#include <gsl/gsl_multimin.h>
#include <gsl/gsl_sf_coupling.h>
#include <gsl/gsl_blas.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>
#include <gsl/gsl_eigen.h>
#include <gsl/gsl_sort.h>
#include <gsl/gsl_sort_vector.h>
#include <gsl/gsl_sf_gamma.h>
#include <gsl/gsl_chebyshev.h>
#include <gsl/gsl_sf_legendre.h>
#include <gsl/gsl_sf_laguerre.h>
#include <gsl/gsl_sf_hyperg.h>
#include <gsl/gsl_sf_pow_int.h>
#include <gsl/gsl_sf_erf.h>
#include <gsl/gsl_linalg.h>
#include <gsl/gsl_integration.h>
#include <gsl/gsl_fft_real.h>
#include <gsl/gsl_fft_halfcomplex.h>
#include <gsl/gsl_bspline.h>
#include <gsl/gsl_odeiv2.h>
#include <gsl/gsl_spline.h>
#include <gsl/gsl_errno.h>
#include <gsl/gsl_fft_complex.h>
#include <gsl/gsl_math.h>
#include <gsl/gsl_roots.h>
#include <armadillo>
using namespace std;

inline double w_mb (double i)
{
    return log(i+i-1.0);
}
/*
  ! This routine calculates the moshinsky vector bracket
  ! Note that D=mass1/mass2
  ! Ref m.sotona and m.gmitro comp.phys.comm 3(1972)53
*/
double gmosh (int n,int l,int nc,int lc,int n1,int l1,int n2,int l2,int lr,double d)
{
    int ip,ixf,ix, iyi, iyf, j1f,j2,k1i,k1f,m1f,iy,m2f,k2,m2,m2i,m1,j1,k2f,k2i,k1;
    double dl, d1l, bb, ba, anorm, y, p, bc, cfac, bm , sm, s, sxy, bxy;

    if((n+n+nc+nc+l+lc-n1-n1-n2-n2-l1-l2) != 0 ) return 0.0;
    if((l+lc-lr) < 0 ) return 0.0;
    if((l1+l2-lr) < 0 ) return 0.0;
    if((abs(l-lc)-lr) > 0 ) return 0.0;
    if((abs(l1-l2)-lr) > 0 ) return 0.0;
    dl=log(d);
    d1l=log(d+1.);
    bb=gsl_sf_lngamma(n1+1)+gsl_sf_lngamma(n2+1)+gsl_sf_lngamma(n+1)-gsl_sf_lngamma(nc+1)+ gsl_sf_lngamma(0.5+n1+l1+1)+gsl_sf_lngamma(0.5+n2+l2+1) -gsl_sf_lngamma(0.5+n+l+1)-gsl_sf_lngamma(0.5+nc+lc+1);
    ba=w_mb(l1+1)+w_mb(l2+1)+w_mb(lc+1)+w_mb(l+1)+
         gsl_sf_lngamma(l1+l2-lr+1)+gsl_sf_lngamma(l+lc+lr+2)
         +gsl_sf_lngamma(l+lc-lr+1)+gsl_sf_lngamma(lc+lr-l+1)+
         gsl_sf_lngamma(lr+l-lc+1)-gsl_sf_lngamma(l1+l2+lr+2)
         -gsl_sf_lngamma(l1+lr-l2+1)-gsl_sf_lngamma(l2+lr-l1+1)-double(l)*d1l;
    ip=lr+n+n1+n2;
    p=1+2*(ip/2*2-ip);
    anorm=p*exp(0.5*(bb+ba));
    y=0.;
    j1f=l+1;
    for (j1=1;j1<=j1f;j1++)
    {
        j2=l+2-j1;
        k1i=abs(l1-j1+1)+1;
        k1f=l1+j1;
        for (k1=k1i;k1<=k1f;k1+=2)
        {
            m1f=n1-(j1+k1-l1)/2+2;
            if((m1f-1) < 0 ) continue;
            k2i=max(abs(l2-j2+1),abs(lc-k1+1))+1;
            k2f=min(l2+j2,lc+k1);
            if((k2i-k2f) > 0 ) continue;
            for (k2=k2i;k2<=k2f;k2+=2)
            {
                m2f=n2-(j2+k2-l2)/2+2;
                if((m2f-1) < 0 ) continue;
                ip=j2-1+(l1+k1+j1+l2+k2+j2)/2;
                p=1+2*(ip/2*2-ip);
                bc=0.5*(double(k1+j2-2)*dl-double(k1+k2-2)*d1l)
                    +gsl_sf_lngamma(k1+l1-j1+1)+gsl_sf_lngamma(k1+k2-lc-1)+
                    gsl_sf_lngamma(k2+l2-j2+1)-gsl_sf_lngamma(k1+l1+j1)-gsl_sf_lngamma(k1+k2+lc)-
                    gsl_sf_lngamma(k2+l2+j2)+w_mb(k1)+w_mb(k2)+gsl_sf_lngamma((k1+l1+j1)/2)+
                    gsl_sf_lngamma((k1+k2+lc)/2)+gsl_sf_lngamma((k2+l2+j2)/2)-
                    gsl_sf_lngamma((k1+l1-j1)/2+1)-gsl_sf_lngamma((l1+j1-k1)/2+1)-
                    gsl_sf_lngamma((j1+k1-l1)/2)-gsl_sf_lngamma((k1+k2-lc)/2)-
                    gsl_sf_lngamma((k2+lc-k1)/2+1)-gsl_sf_lngamma((lc+k1-k2)/2+1)
                    -gsl_sf_lngamma((k2+l2-j2)/2+1)-gsl_sf_lngamma((l2+j2-k2)/2+1)-
                    gsl_sf_lngamma((j2+k2-l2)/2);
                cfac=p*exp(bc);
                sxy=0.;
                ixf=min(k1+k1,k1+k2-lc)-1;
                for (ix=1;ix<=ixf;ix++)
                {
                    iyi=max(1,ix+j1+l2-k1-lr);
                    iyf=min(min(l2+l2+1,l1+l2-lr+1),l2+lc+ix-k1-j2+2);
                    if((iyi-iyf) > 0 ) continue;
                    for (iy=iyi;iy<=iyf;iy++)
                    {
                        ip=ix+iy;
                        p=1+2*(ip/2*2-ip);
                        bxy=gsl_sf_lngamma(k1+k1-ix)+gsl_sf_lngamma(l2+l2-iy+2)+
                            gsl_sf_lngamma(k2+lc-k1+ix)+gsl_sf_lngamma(l1+lr-l2+iy)
                            -gsl_sf_lngamma(ix)-gsl_sf_lngamma(iy)-gsl_sf_lngamma(k1+k2-lc-ix)-
                            gsl_sf_lngamma(l1+l2-lr-iy+2)-gsl_sf_lngamma(k1-l2+lr-j1+iy-ix+1)-
                            gsl_sf_lngamma(l2-k1+lc-j2+ix-iy+3);
                        sxy=sxy+p*exp(bxy);
                    }
                }
                s=cfac*sxy;
                sm=0.;
                for (m1=1;m1<=m1f;m1++)
                {
                    m2i=max(1,nc-m1-(k1+k2-lc)/2+3);
                    if((m2i-m2f) > 0 ) continue;
                    for (m2=m2i;m2<=m2f;m2++)
                    {
                        ip=m1+m2;
                        p=1+2*(ip/2*2-ip);
                        bm=double(m1-1)*dl-double(m1+m2-2)*d1l+gsl_sf_lngamma(0.5+1)
                            +gsl_sf_lngamma(0.5+m1+m2+(k1+k2+lc)/2-2)-gsl_sf_lngamma(0.5+k1+m1-1)-
                            gsl_sf_lngamma(0.5+k2+m2-1)+gsl_sf_lngamma(m1+m2+(k1+k2-lc)/2-2)-
                            gsl_sf_lngamma(m1)-gsl_sf_lngamma(m2)-gsl_sf_lngamma(n1-m1-(j1+k1-l1)/2+3)-
                            gsl_sf_lngamma(n2-m2-(j2+k2-l2)/2+3)
                            -gsl_sf_lngamma(m1+m2-nc+(k1+k2-lc)/2-2);
                        sm=sm+p*exp(bm);
                    }
                }
                y=y+s*sm;
            }
        }
    }
    return anorm*y;

}

int main ()
{
    cout<<"hello world!"<<endl;

    return 1;
}
