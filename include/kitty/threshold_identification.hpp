/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/


#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <cstdlib>
#include <string>
#include <fstream>
#include <iostream>
#include <cassert>
#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "isop.hpp"
#include "traits.hpp"
#include "constructors.hpp"
#include "operations.hpp"
#include "properties.hpp"
#include "cube.hpp"
#include "implicant.hpp"
#include "bit_operations.hpp"
#include "print.hpp"





namespace kitty {

    template<typename TT, typename = std::enable_if_t <kitty::is_complete_truth_table<TT>::value>>
    bool is_threshold(const TT &tt, std::vector <int64_t> *plf = nullptr) {

        std::vector <int64_t> linear_form;
        std::vector <int8_t> negative_unate; 
        TT tt0 = tt;
        for (auto i = 0u; i < tt.num_vars(); i++) {

            bool neg_unate = is_negative_unate_in_i(tt, i);
            if (is_positive_unate_in_i(tt, i) + neg_unate == 0) {
                return false;
            }
            if (neg_unate) {
                flip_inplace(tt0, i);
                negative_unate.push_back(i);
            }

        }
        std::vector <kitty::cube> positiveConst = isop(tt0);
        std::vector <kitty::cube> negativeConst = isop(unary_not(tt0));

        lprec *lp;
        int Numcol, *colnb = NULL, ret = 0;
        REAL *row = NULL;
        Numcol = tt.num_vars() + 1;

        lp = make_lp(0, Numcol);
        if (lp == NULL) {
            return false; 
        }

        colnb = (int *) malloc(Numcol * sizeof(*colnb));
        row = (REAL *) malloc(Numcol * sizeof(*row));

        if ((colnb == NULL) || (row == NULL)) {
            return false;
        }
        if (ret == 0) {
            for (unsigned int j = 0; j <= tt.num_vars(); j++) {
                colnb[0] = j + 1;
                row[j] = 1;
                add_constraintex(lp, 1, row, colnb, GE, 0);
            }
        }
        if (ret == 0) {
            for (auto k = 0; k < positiveConst.size(); k++) {
                kitty::cube pos = positiveConst.at(k);
                for (auto i = 0; i < tt.num_vars(); i++) {
                    bool cond = pos.get_mask(i) && pos.get_bit(i); 
                    colnb[i] = i + 1;
                    if (cond == 1) {
                        row[i] = 1;
                    } else {
                        row[i] = 0;
                    }
                }
                colnb[tt.num_vars()] = tt.num_vars() + 1; 
                row[tt.num_vars()] = -1.0;
                add_constraintex(lp, Numcol, row, colnb, GE, 0);
            }
        }
        if (ret == 0) {
            for (auto k = 0; k < negativeConst.size(); k++) {
                kitty::cube neg = negativeConst.at(k);
                for (auto i = 0; i < tt.num_vars(); i++) {
                    colnb[i] = i + 1;
                    bool cond = !neg.get_mask(i) || (neg.get_mask(i) && neg.get_bit(i)); 
                    if (cond) {
                        row[i] = 1.0;
                    } else {
                        row[i] = 0.0;
                    }
                }
                colnb[tt.num_vars()] = tt.num_vars() + 1;
                row[tt.num_vars()] = -1.0;
                add_constraintex(lp, Numcol, row, colnb, LE, -1);
            }
        }
        if (ret == 0) {
            set_add_rowmode(lp, FALSE); 
            for (int j = 0; j < Numcol; j++) {
                colnb[j] = j + 1;
                row[j] = 1;
            }
            set_obj_fnex(lp, Numcol, row, colnb);
        }
        set_minim(lp);
        set_verbose(lp, IMPORTANT);
        ret = solve(lp);
        if (ret != 0) {
            return false;
        } else {
            get_variables(lp, row);
            for (int i = 0; i < Numcol; i++) {
                linear_form.push_back((int64_t) row[i]);
            }
            for (auto i : negative_unate) {
                linear_form.at(i) = -linear_form.at(i);
                linear_form[Numcol - 1] = linear_form[Numcol - 1] + linear_form[i];
            }
            *plf = linear_form;
            if (colnb != NULL)
                free(colnb);
            if (row != NULL)
                free(row);
            if (lp != NULL)
                delete_lp(lp);
            return true;
        }
    }
    
    template<typename TT, typename = std::enable_if_t <kitty::is_complete_truth_table<TT>::value>>
    bool is_negative_unate_in_i(const TT &tt, uint8_t i) {
        auto const tt0 = cofactor0(tt, i);
        auto const tt1 = cofactor1(tt, i);
        for (auto bit = 0; bit < (2 << (tt.num_vars() - 1)); bit++) {
            if (get_bit(tt0, bit) >= get_bit(tt1, bit)) {
                continue;
            } else {
                return false;
            }
        }
        return true;
    }

    template<typename TT, typename = std::enable_if_t <kitty::is_complete_truth_table<TT>::value>>
    bool is_positive_unate_in_i(const TT &tt, uint8_t i) {
        auto const tt0 = cofactor0(tt, i);
        auto const tt1 = cofactor1(tt, i);
        for (auto bit = 0; bit < (2 << (tt.num_vars() - 1)); bit++) {
            if (get_bit(tt0, bit) <= get_bit(tt1, bit)) {
                continue;
            } else {
                return false;
            }
        }
        return true;
    }

}

