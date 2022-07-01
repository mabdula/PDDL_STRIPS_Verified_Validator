#!/bin/bash

../pddl_validate_plan <(tr A-Z a-z < $1) <(tr A-Z a-z < $2) <(tr A-Z a-z < $3)
