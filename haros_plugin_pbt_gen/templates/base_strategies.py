def ros_bool():
    return strategies.booleans()

def ros_uint8(min_value=0, max_value=UINT8_MAX_VALUE):
    if (min_value < 0 or min_value > UINT8_MAX_VALUE or max_value < 0
            or max_value > UINT8_MAX_VALUE or min_value > max_value):
        raise ValueError('values out of bounds: {}, {}'.format(
            min_value, max_value))
    return strategies.integers(min_value=max(min_value, 0),
                               max_value=min(max_value, UINT8_MAX_VALUE))

ros_char = ros_uint8

def ros_int8(min_value=INT8_MIN_VALUE, max_value=INT8_MAX_VALUE):
    if (min_value < INT8_MIN_VALUE or min_value > INT8_MAX_VALUE
            or max_value < INT8_MIN_VALUE or max_value > INT8_MAX_VALUE
            or min_value > max_value):
        raise ValueError('values out of bounds: {}, {}'.format(
            min_value, max_value))
    return strategies.integers(min_value=max(min_value, INT8_MIN_VALUE),
                               max_value=min(max_value, INT8_MAX_VALUE))

ros_byte = ros_int8

def ros_uint16(min_value=0, max_value=UINT16_MAX_VALUE):
    if (min_value < 0 or min_value > UINT16_MAX_VALUE or max_value < 0
            or max_value > UINT16_MAX_VALUE or min_value > max_value):
        raise ValueError('values out of bounds: {}, {}'.format(
            min_value, max_value))
    return strategies.integers(min_value=max(min_value, 0),
                               max_value=min(max_value, UINT16_MAX_VALUE))

def ros_int16(min_value=INT16_MIN_VALUE, max_value=INT16_MAX_VALUE):
    if (min_value < INT16_MIN_VALUE or min_value > INT16_MAX_VALUE
            or max_value < INT16_MIN_VALUE or max_value > INT16_MAX_VALUE
            or min_value > max_value):
        raise ValueError('values out of bounds: {}, {}'.format(
            min_value, max_value))
    return strategies.integers(min_value=max(min_value, INT16_MIN_VALUE),
                               max_value=min(max_value, INT16_MAX_VALUE))

def ros_uint32(min_value=0, max_value=UINT32_MAX_VALUE):
    if (min_value < 0 or min_value > UINT32_MAX_VALUE or max_value < 0
            or max_value > UINT32_MAX_VALUE or min_value > max_value):
        raise ValueError('values out of bounds: {}, {}'.format(
            min_value, max_value))
    return strategies.integers(min_value=max(min_value, 0),
                               max_value=min(max_value, UINT32_MAX_VALUE))

def ros_int32(min_value=INT32_MIN_VALUE, max_value=INT32_MAX_VALUE):
    if (min_value < INT32_MIN_VALUE or min_value > INT32_MAX_VALUE
            or max_value < INT32_MIN_VALUE or max_value > INT32_MAX_VALUE
            or min_value > max_value):
        raise ValueError('values out of bounds: {}, {}'.format(
            min_value, max_value))
    return strategies.integers(min_value=max(min_value, INT32_MIN_VALUE),
                               max_value=min(max_value, INT32_MAX_VALUE))

def ros_uint64(min_value=0, max_value=UINT64_MAX_VALUE):
    if (min_value < 0 or min_value > UINT64_MAX_VALUE or max_value < 0
            or max_value > UINT64_MAX_VALUE or min_value > max_value):
        raise ValueError('values out of bounds: {}, {}'.format(
            min_value, max_value))
    return strategies.integers(min_value=max(min_value, 0),
                               max_value=min(max_value, UINT64_MAX_VALUE))

def ros_int64(min_value=INT64_MIN_VALUE, max_value=INT64_MAX_VALUE):
    if (min_value < INT64_MIN_VALUE or min_value > INT64_MAX_VALUE
            or max_value < INT64_MIN_VALUE or max_value > INT64_MAX_VALUE
            or min_value > max_value):
        raise ValueError('values out of bounds: {}, {}'.format(
            min_value, max_value))
    return strategies.integers(min_value=max(min_value, INT64_MIN_VALUE),
                               max_value=min(max_value, INT64_MAX_VALUE))


def ros_float32(min_value=FLOAT32_MIN_VALUE, max_value=FLOAT32_MAX_VALUE):
    if (min_value < FLOAT32_MIN_VALUE or min_value > FLOAT32_MAX_VALUE
            or max_value < FLOAT32_MIN_VALUE or max_value > FLOAT32_MAX_VALUE
            or min_value > max_value):
        raise ValueError('values out of bounds: {}, {}'.format(
            min_value, max_value))
    return strategies.floats(min_value=max(min_value, FLOAT32_MIN_VALUE),
                             max_value=min(max_value, FLOAT32_MAX_VALUE),
                             width=32)


def ros_float64(min_value=FLOAT64_MIN_VALUE, max_value=FLOAT64_MAX_VALUE):
    if (min_value < FLOAT64_MIN_VALUE or min_value > FLOAT64_MAX_VALUE
            or max_value < FLOAT64_MIN_VALUE or max_value > FLOAT64_MAX_VALUE
            or min_value > max_value):
        raise ValueError('values out of bounds: {}, {}'.format(
            min_value, max_value))
    return strategies.floats(min_value=max(min_value, FLOAT64_MIN_VALUE),
                             max_value=min(max_value, FLOAT64_MAX_VALUE),
                             width=64)

def ros_string():
    return strategies.binary(min_size=0, max_size=256)

@strategies.composite
def ros_time(draw):
    secs = draw(strategies.integers(min_value=0, max_value=4294967295))
    nsecs = draw(strategies.integers(min_value=0, max_value=4294967295))
    return rospy.Time(secs, nsecs)

@strategies.composite
def ros_duration(draw):
    secs = draw(strategies.integers(min_value=-2147483648,
                                    max_value=2147483647))
    nsecs = draw(strategies.integers(min_value=-2147483648,
                                     max_value=2147483647))
    return rospy.Duration(secs, nsecs)
