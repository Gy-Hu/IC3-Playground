/**
 * @file tests/main_tests/kde_test.cpp
 * @author Roberto Hueso
 *
 * Test mlpackMain() of kde_main.cpp
 *
 * mlpack is free software; you may redistribute it and/or modify it under the
 * terms of the 3-clause BSD license.  You should have received a copy of the
 * 3-clause BSD license along with mlpack.  If not, see
 * http://www.opensource.org/licenses/BSD-3-Clause for more information.
 */
#include <string>

#define BINDING_TYPE BINDING_TYPE_TEST

static const std::string testName = "KDE";

#include <mlpack/core.hpp>
#include <mlpack/core/util/mlpack_main.hpp>
#include "test_helper.hpp"
#include <mlpack/methods/kde/kde_main.cpp>

#include "../catch.hpp"

using namespace mlpack;

struct KDETestFixture
{
 public:
  KDETestFixture()
  {
    // Cache in the options for this program.
    IO::RestoreSettings(testName);
  }

  ~KDETestFixture()
  {
    // Clear the settings.
    bindings::tests::CleanMemory();
    IO::ClearSettings();
  }
};

void ResetKDESettings()
{
  IO::ClearSettings();
  IO::RestoreSettings(testName);
}

/**
  * Ensure that the estimations we get for KDEMain, are the same as the ones we
  * get from the KDE class without any wrappers. Requires normalization.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEGaussianRTreeResultsMain",
                "[KDEMainTest][BindingTests]")
{
  // Datasets.
  arma::mat reference = arma::randu(3, 500);
  arma::mat query = arma::randu(3, 100);
  arma::vec kdeEstimations, mainEstimations;
  double kernelBandwidth = 1.5;
  double relError = 0.05;

  kernel::GaussianKernel kernel(kernelBandwidth);
  metric::EuclideanDistance metric;
  KDE<kernel::GaussianKernel,
      metric::EuclideanDistance,
      arma::mat,
      tree::RTree>
      kde(relError, 0.0, kernel, KDEMode::DUAL_TREE_MODE, metric);
  kde.Train(reference);
  kde.Evaluate(query, kdeEstimations);
  // Normalize estimations.
  kdeEstimations /= kernel.Normalizer(reference.n_rows);

  // Main estimations.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("kernel", std::string("gaussian"));
  SetInputParam("tree", std::string("r-tree"));
  SetInputParam("rel_error", relError);
  SetInputParam("bandwidth", kernelBandwidth);

  mlpackMain();

  mainEstimations = std::move(IO::GetParam<arma::vec>("predictions"));

  // Check whether results are equal.
  for (size_t i = 0; i < query.n_cols; ++i)
    REQUIRE(kdeEstimations[i] == Approx( mainEstimations[i]).epsilon(relError));
}

/**
  * Ensure that the estimations we get for KDEMain, are the same as the ones we
  * get from the KDE class without any wrappers. Doesn't require normalization.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDETriangularBallTreeResultsMain",
                "[KDEMainTest][BindingTests]")
{
  // Datasets.
  arma::mat reference = arma::randu(3, 300);
  arma::mat query = arma::randu(3, 100);
  arma::vec kdeEstimations, mainEstimations;
  double kernelBandwidth = 3.0;
  double relError = 0.06;

  kernel::TriangularKernel kernel(kernelBandwidth);
  metric::EuclideanDistance metric;
  KDE<kernel::TriangularKernel,
      metric::EuclideanDistance,
      arma::mat,
      tree::BallTree>
      kde(relError, 0.0, kernel, KDEMode::DUAL_TREE_MODE, metric);
  kde.Train(reference);
  kde.Evaluate(query, kdeEstimations);

  // Main estimations.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("kernel", std::string("triangular"));
  SetInputParam("tree", std::string("ball-tree"));
  SetInputParam("rel_error", relError);
  SetInputParam("bandwidth", kernelBandwidth);

  mlpackMain();

  mainEstimations = std::move(IO::GetParam<arma::vec>("predictions"));

  // Check whether results are equal.
  for (size_t i = 0; i < query.n_cols; ++i)
    REQUIRE(kdeEstimations[i] == Approx( mainEstimations[i]).epsilon(relError));
}

/**
  * Ensure that the estimations we get for KDEMain, are the same as the ones we
  * get from the KDE class without any wrappers in the monochromatic case.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMonoResultsMain",
                "[KDEMainTest][BindingTests]")
{
  // Datasets.
  arma::mat reference = arma::randu(2, 300);
  arma::vec kdeEstimations, mainEstimations;
  double kernelBandwidth = 2.3;
  double relError = 0.05;

  kernel::EpanechnikovKernel kernel(kernelBandwidth);
  metric::EuclideanDistance metric;
  KDE<kernel::EpanechnikovKernel,
      metric::EuclideanDistance,
      arma::mat,
      tree::StandardCoverTree>
    kde(relError, 0.0, kernel, KDEMode::DUAL_TREE_MODE, metric);
  kde.Train(reference);
  // Perform monochromatic KDE.
  kde.Evaluate(kdeEstimations);
  // Normalize.
  kdeEstimations /= kernel.Normalizer(reference.n_rows);

  // Main estimations.
  SetInputParam("reference", reference);
  SetInputParam("kernel", std::string("epanechnikov"));
  SetInputParam("tree", std::string("cover-tree"));
  SetInputParam("rel_error", relError);
  SetInputParam("bandwidth", kernelBandwidth);

  mlpackMain();

  mainEstimations = std::move(IO::GetParam<arma::vec>("predictions"));

  // Check whether results are equal.
  for (size_t i = 0; i < reference.n_cols; ++i)
    REQUIRE(kdeEstimations[i] == Approx( mainEstimations[i]).epsilon(relError));
}

/**
  * Ensuring that absence of input data is checked.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDENoInputData",
                "[KDEMainTest][BindingTests]")
{
  // No input data is not provided. Should throw a runtime error.
  Log::Fatal.ignoreInput = true;
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);
  Log::Fatal.ignoreInput = false;
}

/**
  * Check result has as many densities as query points.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEOutputSize",
                "[KDEMainTest][BindingTests]")
{
  const size_t dim = 3;
  const size_t samples = 110;
  arma::mat reference = arma::randu<arma::mat>(dim, 325);
  arma::mat query = arma::randu<arma::mat>(dim, samples);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);

  mlpackMain();
  // Check number of output elements.
  REQUIRE(IO::GetParam<arma::vec>("predictions").size() == samples);
}

/**
  * Check that saved model can be reused.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEModelReuse",
                "[KDEMainTest][BindingTests]")
{
  const size_t dim = 3;
  const size_t samples = 100;
  const double relError = 0.05;
  arma::mat reference = arma::randu<arma::mat>(dim, 300);
  arma::mat query = arma::randu<arma::mat>(dim, samples);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("bandwidth", 2.4);
  SetInputParam("rel_error", 0.05);

  mlpackMain();

  arma::vec oldEstimations = std::move(IO::GetParam<arma::vec>("predictions"));

  // Change parameters and load model.
  IO::GetSingleton().Parameters()["reference"].wasPassed = false;
  SetInputParam("query", query);
  SetInputParam("input_model",
      std::move(IO::GetParam<KDEModel*>("output_model")));

  mlpackMain();

  arma::vec newEstimations = std::move(IO::GetParam<arma::vec>("predictions"));

  // Check estimations are the same.
  for (size_t i = 0; i < samples; ++i)
    REQUIRE(oldEstimations[i] == Approx( newEstimations[i]).epsilon(relError));
}

/**
  * Ensure that the estimations we get for KDEMain, are the same as the ones we
  * get from the KDE class without any wrappers using single-tree mode.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEGaussianSingleKDTreeResultsMain",
                "[KDEMainTest][BindingTests]")
{
  // Datasets.
  arma::mat reference = arma::randu(3, 400);
  arma::mat query = arma::randu(3, 400);
  arma::vec kdeEstimations, mainEstimations;
  double kernelBandwidth = 3.0;
  double relError = 0.06;

  kernel::GaussianKernel kernel(kernelBandwidth);
  metric::EuclideanDistance metric;
  KDE<kernel::GaussianKernel,
      metric::EuclideanDistance,
      arma::mat,
      tree::BallTree>
      kde(relError, 0.0, kernel, KDEMode::SINGLE_TREE_MODE, metric);
  kde.Train(reference);
  kde.Evaluate(query, kdeEstimations);
  kdeEstimations /= kernel.Normalizer(reference.n_rows);

  // Main estimations.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("kernel", std::string("gaussian"));
  SetInputParam("tree", std::string("kd-tree"));
  SetInputParam("algorithm", std::string("single-tree"));
  SetInputParam("rel_error", relError);
  SetInputParam("bandwidth", kernelBandwidth);

  mlpackMain();

  mainEstimations = std::move(IO::GetParam<arma::vec>("predictions"));

  // Check whether results are equal.
  for (size_t i = 0; i < query.n_cols; ++i)
    REQUIRE(kdeEstimations[i] == Approx( mainEstimations[i]).epsilon(relError));
}

/**
  * Ensure we get an exception when an invalid kernel is specified.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainInvalidKernel",
                "[KDEMainTest][BindingTests]")
{
  arma::mat reference = arma::randu<arma::mat>(2, 10);
  arma::mat query = arma::randu<arma::mat>(2, 5);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("kernel", std::string("linux"));

  Log::Fatal.ignoreInput = true;
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);
  Log::Fatal.ignoreInput = false;
}

/**
  * Ensure we get an exception when an invalid tree is specified.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainInvalidTree",
                "[KDEMainTest][BindingTests]")
{
  arma::mat reference = arma::randu<arma::mat>(2, 10);
  arma::mat query = arma::randu<arma::mat>(2, 5);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("tree", std::string("olive"));

  Log::Fatal.ignoreInput = true;
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);
  Log::Fatal.ignoreInput = false;
}

/**
  * Ensure we get an exception when an invalid algorithm is specified.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainInvalidAlgorithm",
                "[KDEMainTest][BindingTests]")
{
  arma::mat reference = arma::randu<arma::mat>(2, 10);
  arma::mat query = arma::randu<arma::mat>(2, 5);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("algorithm", std::string("bogosort"));

  Log::Fatal.ignoreInput = true;
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);
  Log::Fatal.ignoreInput = false;
}

/**
  * Ensure we get an exception when both reference and input_model are
  * specified.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainReferenceAndModel",
                "[KDEMainTest][BindingTests]")
{
  arma::mat reference = arma::randu<arma::mat>(2, 10);
  arma::mat query = arma::randu<arma::mat>(2, 5);
  KDEModel* model = new KDEModel();

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("input_model", model);

  Log::Fatal.ignoreInput = true;
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);
  Log::Fatal.ignoreInput = false;
}

/**
  * Ensure we get an exception when an invalid absolute error is specified.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainInvalidAbsoluteError",
                "[KDEMainTest][BindingTests]")
{
  arma::mat reference = arma::randu<arma::mat>(1, 10);
  arma::mat query = arma::randu<arma::mat>(1, 5);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);

  Log::Fatal.ignoreInput = true;
  // Invalid value.
  SetInputParam("abs_error", -0.1);
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);

  // Valid value.
  SetInputParam("abs_error", 5.8);
  REQUIRE_NOTHROW(mlpackMain());
  Log::Fatal.ignoreInput = false;
}

/**
  * Ensure we get an exception when an invalid relative error is specified.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainInvalidRelativeError",
                "[KDEMainTest][BindingTests]")
{
  arma::mat reference = arma::randu<arma::mat>(1, 10);
  arma::mat query = arma::randu<arma::mat>(1, 5);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);

  Log::Fatal.ignoreInput = true;
  // Invalid under 0.
  SetInputParam("rel_error", -0.1);
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);

  // Invalid over 1.
  SetInputParam("rel_error", 1.1);
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);

  // Valid value.
  SetInputParam("rel_error", 0.3);
  REQUIRE_NOTHROW(mlpackMain());
  Log::Fatal.ignoreInput = false;
}

/**
  * Ensure we get an exception when an invalid Monte Carlo probability is
  * specified.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainInvalidMCProbability",
                "[KDEMainTest][BindingTests]")
{
  arma::mat reference = arma::randu<arma::mat>(1, 10);
  arma::mat query = arma::randu<arma::mat>(1, 5);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("kernel", std::string("gaussian"));
  SetInputParam("monte_carlo", true);

  Log::Fatal.ignoreInput = true;
  // Invalid under 0.
  SetInputParam("mc_probability", -0.1);
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);

  // Invalid over 1.
  SetInputParam("mc_probability", 1.1);
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);

  // Valid value.
  SetInputParam("mc_probability", 0.3);
  REQUIRE_NOTHROW(mlpackMain());
  Log::Fatal.ignoreInput = false;
}

/**
  * Ensure we get an exception when an invalid Monte Carlo initial sample size
  * is specified.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainInvalidMCInitialSampleSize",
                "[KDEMainTest][BindingTests]")
{
  arma::mat reference = arma::randu<arma::mat>(1, 10);
  arma::mat query = arma::randu<arma::mat>(1, 5);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("kernel", std::string("gaussian"));
  SetInputParam("monte_carlo", true);

  Log::Fatal.ignoreInput = true;
  // Invalid under 0.
  SetInputParam("initial_sample_size", -1);
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);

  // Invalid 0.
  SetInputParam("initial_sample_size", 0);
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);

  // Valid value.
  SetInputParam("initial_sample_size", 20);
  REQUIRE_NOTHROW(mlpackMain());
  Log::Fatal.ignoreInput = false;
}

/**
  * Ensure we get an exception when an invalid Monte Carlo entry coefficient
  * is specified.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainInvalidMCEntryCoef",
                "[KDEMainTest][BindingTests]")
{
  arma::mat reference = arma::randu<arma::mat>(1, 10);
  arma::mat query = arma::randu<arma::mat>(1, 5);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("kernel", std::string("gaussian"));
  SetInputParam("monte_carlo", true);

  Log::Fatal.ignoreInput = true;
  // Invalid under 1.
  SetInputParam("mc_entry_coef", 0.5);
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);

  // Valid greater than 1.
  SetInputParam("mc_entry_coef", 1.1);
  REQUIRE_NOTHROW(mlpackMain());
  Log::Fatal.ignoreInput = false;
}

/**
  * Ensure we get an exception when an invalid Monte Carlo break coefficient
  * is specified.
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainInvalidMCBreakCoef",
                "[KDEMainTest][BindingTests]")
{
  arma::mat reference = arma::randu<arma::mat>(1, 10);
  arma::mat query = arma::randu<arma::mat>(1, 5);

  // Main params.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  SetInputParam("kernel", std::string("gaussian"));
  SetInputParam("monte_carlo", true);

  Log::Fatal.ignoreInput = true;
  // Invalid under 0.
  SetInputParam("mc_break_coef", -0.5);
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);

  // Valid between 0 and 1.
  SetInputParam("mc_break_coef", 0.3);
  REQUIRE_NOTHROW(mlpackMain());

  // Invalid greater than 1.
  SetInputParam("mc_break_coef", 1.1);
  REQUIRE_THROWS_AS(mlpackMain(), std::runtime_error);
  Log::Fatal.ignoreInput = false;
}

/**
  * Ensure when --monte_carlo flag is true, then KDEMain actually uses Monte
  * Carlo estimations. Since this test has a random component, it might fail
  * (although it's unlikely).
 **/
TEST_CASE_METHOD(KDETestFixture, "KDEMainMonteCarloFlag",
                "[KDEMainTest][BindingTests]")
{
  // Datasets.
  arma::mat reference = arma::randu(1, 5000);
  arma::mat query = arma::randu(1, 300);
  arma::vec estimations1, estimations2, differences;
  double kernelBandwidth = 0.2;

  // Parameters for estimations.
  SetInputParam("reference", arma::mat(reference));
  SetInputParam("query", arma::mat(query));
  SetInputParam("kernel", std::string("gaussian"));
  SetInputParam("tree", std::string("kd-tree"));
  SetInputParam("bandwidth", kernelBandwidth);
  SetInputParam("monte_carlo", true);

  // Compute estimations 1.
  mlpackMain();
  estimations1 = std::move(IO::GetParam<arma::vec>("predictions"));

  delete IO::GetParam<KDEModel*>("output_model");

  // Compute estimations 2.
  SetInputParam("reference", reference);
  SetInputParam("query", query);
  mlpackMain();
  estimations2 = std::move(IO::GetParam<arma::vec>("predictions"));

  // Check whether results are equal.
  differences = arma::abs(estimations1 - estimations2);
  const double sumDifferences = arma::accu(differences);
  REQUIRE(sumDifferences > 0);
}
