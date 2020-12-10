r"""
Additive rational multivariate functions

This module implements the algebra generated by rational functions of the form

.. MATH::

    \frac{P}{\prod L_i^{d_i}}

where the `L_i` are linear forms (ie homogeneous degree one) and `d_i` are positive integers.
"""
#*****************************************************************************
#       Copyright (C) 2019 Vincent Delecroix <20100.delecroix@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  https://www.gnu.org/licenses/
#*****************************************************************************

from six.moves import range, map, filter, zip
from six import iteritems

from .factored_denominator import FactoredDenominator, AbstractMSum, AbstractMSumRing, laurent_monomial

import numbers

from sage.misc.cachefunc import cached_method
from sage.rings.rational_field import QQ

class AdditiveMultivariateGeneratingSeries(AbstractMSum):
    r"""
    EXAMPLES::

        sage: from surface_dynamics.misc.additive_multivariate_generating_series import AdditiveMultivariateGeneratingSeriesRing

        sage: A = AdditiveMultivariateGeneratingSeriesRing('x', 3)
    """
    def integral_sum_as_mzv(self):
        r"""
        Make the sum over all possible positive integers and express
        the result as a linear combination of multiple zeta values.

        EXAMPLES::

            sage: from surface_dynamics.misc.additive_multivariate_generating_series import AdditiveMultivariateGeneratingSeriesRing

            sage: A = AdditiveMultivariateGeneratingSeriesRing('x', 3)
            sage: f = A.term(1, [((1,0,0),2), ((0,1,0),2), ((0,0,1),2)])
            sage: f.integral_sum_as_mzv()
            36*ζ(1,1,4) + 24*ζ(1,2,3) + 12*ζ(1,3,2) + 12*ζ(2,1,3) + 6*ζ(2,2,2)
        """
        from .generalized_multiple_zeta_values import handle_term
        n = self.parent().free_module().rank()
        return sum(QQ(num) * handle_term(n, den._tuple) for den, num in self._data.items())

    def _den_str(self, den):
        var_names = self.parent().polynomial_ring().variable_names()
        return den.str_linear(var_names)

    def factor(self):
        """
        Group all the partial fractions into a unique fraction.

        EXAMPLES::

            sage: from surface_dynamics.misc.additive_multivariate_generating_series import AdditiveMultivariateGeneratingSeriesRing

            sage: A = AdditiveMultivariateGeneratingSeriesRing('x', 3)

            sage: f = A.term(1, [([1,3,0],1),([1,0,-1],1)])
            sage: g = A.term(1, [([1,1,0],1),([1,0,-1],2)])
            sage: (f + g).factor()
            (x0^2 + x0*x1 - x0*x2 - x1*x2 + x0 + 3*x1)/((x0 - x2)^2*(x0 + x1)*(x0 + 3*x1))

        Simplification::

            sage: x0, x1, x2 = A.polynomial_ring().gens()
            sage: f1 = A.term(1, [([1,0,0],1)])
            sage: f2 = A.term(1, [([0,1,0],1)])
            sage: f3 = A.term(x0 + x1, [([1,0,0],1), ([0,1,0],1)])
            sage: (f1 + f2 - f3).factor()
            0

            sage: f1 + f2 == f3  # indirect doctest
            True
        """
        M = self.parent()

        # compute the product of denominators
        V = M.free_module()
        D = FactoredDenominator([], V)
        for den, num in self._data.items():
            D.lcm_update(den)

        P = M.polynomial_ring()
        N = P.zero()
        for den,num in self._data.items():
            N += num * (D / den).to_additive_polynomial(P)

        # Look for simplifications
        N = P(N)
        gt = False
        for mon,mult in list(D._dict.items()):
            pmon = sum(coeff * P.gen(i) for i,coeff in enumerate(mon))
            q,r = N.quo_rem(pmon)
            while mult and not r:
                gt = True
                mult -= 1
                N = q
                q,r = N.quo_rem(pmon)

            if mult:
                D._dict[mon] = mult
            else:
                del D._dict[mon]

        if gt:
            D._tuple = tuple(sorted(D._dict.items()))

        return M.term(N, D)

class AdditiveMultivariateGeneratingSeriesRing(AbstractMSumRing):
    Element = AdditiveMultivariateGeneratingSeries

    @staticmethod
    def __classcall__(cls, *args):
        if len(args) == 1 and isinstance(args[0], AbstractMSumRing):
            poly_ring = args[0]._polynomial_ring
        else:
            if len(args) == 1 and not isinstance(args[0], (tuple, str)):
                args = (tuple(args[0]),)
            from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
            poly_ring = PolynomialRing(QQ, *args)

        return super(AbstractMSumRing, cls).__classcall__(cls, poly_ring)

    def _critical_point(self):
        r"""
        EXAMPLES::

            sage: from surface_dynamics.misc.additive_multivariate_generating_series import AdditiveMultivariateGeneratingSeriesRing
            sage: A = AdditiveMultivariateGeneratingSeriesRing('x', 3)
            sage: A._critical_point()
            [0, 0, 0]
        """
        return [self.base_ring().zero()] * self.ngens()

    def _repr_(self):
        vars_string = ', '.join(self.polynomial_ring().variable_names())
        return "Additive multivariate generating series on {}".format(vars_string)

    def _coerce_map_from_(self, other):
        r"""
        EXAMPLES::

            sage: from surface_dynamics.misc.additive_multivariate_generating_series import AdditiveMultivariateGeneratingSeriesRing

            sage: A = AdditiveMultivariateGeneratingSeriesRing('x', 2)

            sage: A.has_coerce_map_from(ZZ)
            True
            sage: A.coerce_map_from(ZZ)
            Co...ion map:
              From: Integer Ring
              To:   Additive multivariate generating series on x0, x1

            sage: A.has_coerce_map_from(QQ)
            True

            sage: A.has_coerce_map_from(A.polynomial_ring())
            True
        """
        if self.polynomial_ring().has_coerce_map_from(other):
            return True
