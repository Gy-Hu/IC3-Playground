//
// Created by galls2 on 26/09/19.
//

#pragma once
#include <exception>
#include <stdexcept>

class OmgException : public std::runtime_error {
public:
    explicit OmgException(const char* message) : std::runtime_error(message) {}
    const char* what() const noexcept override {
        auto base_msg = std::runtime_error::what();
        return base_msg;
    }

};

#define DECLARE_EXCEPTION_TYPE(derived, base) class derived: public base { using base::base; };
#define DECLARE_OMG_EXCEPTION(derived) DECLARE_EXCEPTION_TYPE(derived, OmgException)