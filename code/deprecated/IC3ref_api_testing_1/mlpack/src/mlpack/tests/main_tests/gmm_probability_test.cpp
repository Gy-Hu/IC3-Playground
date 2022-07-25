/**
 * @file tests/main_tests/gmm_probability_test.cpp
 * @author Yashwant Singh
 *
 * Test mlpackMain() of gmm_probability_main.cpp.
 *
 * mlpack is free software; you may redistribute it and/or modify it under the
 * terms of the 3-clause BSD license.  You should have received a copy of the
 * 3-clause BSD license along with mlpack.  If not, see
 * http://www.opensource.org/licenses/BSD-3-Clause for more information.
 */

#define BINDING_TYPE BINDING_TYPE_TEST

static const std::string testName = "GmmProbability";

#include <mlpack/core.hpp>
#include <mlpack/core/util/mlpack_main.hpp>
#include <mlpack/methods/gmm/gmm_probability_main.cpp>

#include "test_helper.hpp"

#include "../catch.hpp"

using namespace mlpack;

struct GmmProbabilityTestFixture
{
 public:
  GmmProbabilityTestFixture()
  {
    // Cache in the options for this program.
    IO::RestoreSettings(testName);
  }

  ~GmmProbabilityTestFixture()
  {
    // Clear the settings.
    IO::ClearSettings();
  }
};

void ResetGmmProbabilitySetting()
{
  IO::ClearSettings();
  IO::RestoreSettings(testName);
}

// Checking the input and output dimensionality.
TEST_CASE_METHOD(GmmProbabilityTestFixture, "GmmProbabilityDimensionality",
                 "[GmmProbabilityMainTest][BindingTests]")
{
  arma::mat inputData(5, 10, arma::fill::randu);

  GMM gmm(1, 5);
  gmm.Train(std::move(inputData), 5);

  arma::mat inputPoints(5, 5, arma::fill::randu);

  SetInputParam("input", std::move(inputPoints));
  SetInputParam("input_model", &gmm);

  mlpackMain();

  REQUIRE(IO::GetParam<arma::mat>("output").n_cols == 5);
  REQUIRE(IO::GetParam<arma::mat>("output").n_rows == 1);
}
